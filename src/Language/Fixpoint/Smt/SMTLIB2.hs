{-# LANGUAGE CPP                       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE QuasiQuotes               #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE PatternGuards             #-}

-- | This module contains an SMTLIB2 interface for
--   1. checking the validity, and,
--   2. computing satisfying assignments
--   for formulas.
--   By implementing a binary interface over the SMTLIB2 format defined at
--   http://www.smt-lib.org/
--   http://www.grammatech.com/resource/smt/SMTLIBTutorial.pdf
--
-- Note [Async SMT API]
--
-- The SMT solver is started in a separate process and liquid-fixpoint
-- communicates with it via pipes. This mechanism introduces some latency
-- since the queries need to reach the buffers in a separate process and
-- the OS has to switch contexts.
--
-- A remedy we currently try for this is to send multiple queries
-- together without waiting for the reply to each one, i.e. asynchronously.
-- We then collect the multiple answers after sending all of the queries.
--
-- The functions named @smt*Async@ implement this scheme.
--
-- An asynchronous thread is used to write the queries to prevent the
-- caller from blocking on IO, should the write buffer be full or should
-- an 'hFlush' call be necessary.
--

module Language.Fixpoint.Smt.SMTLIB2 (

    -- * Typeclass for SMTLIB2 conversion
      SMTLIB2 (..)

    -- * Creating and killing SMTLIB2 Process
    , Context
    , SolveEnv(..)
    , withContext
    , withContextWithSEnv
    , cleanupContext

    -- * Execute Queries
    , command
    , asyncCommand
    , smtRead
    , smtExit

    ) where

import           Control.Concurrent.Async (Async, async, cancel)
import           Control.Concurrent.STM
  (TVar, atomically, modifyTVar, newTVarIO, readTVar, retry, writeTVar)
import           Language.Fixpoint.Types.Config ( SMTSolver (..)
                                                , Config
                                                , solver
                                                , smtTimeout
                                                , gradual
                                                , stringTheory)
import qualified Language.Fixpoint.Misc          as Misc
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types         hiding (allowHO)
import           Language.Fixpoint.Smt.Interface (IsSMTContext(..))
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Smt.Serialize ()
import           Control.Applicative      ((<|>))
import           Control.Monad
import           Control.Exception
import           Data.Char
#if !MIN_VERSION_base(4,14,0)
import           Data.Semigroup          (Semigroup (..))
#endif

import qualified Data.Text                as T
import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           System.Console.CmdArgs.Verbosity
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO
import           System.Process
import qualified Data.Attoparsec.Text     as A
import           Data.Attoparsec.Internal.Types (Parser)
import           Text.PrettyPrint.HughesPJ (text)
import           Language.Fixpoint.Utils.Builder as Builder


-- | Information about the external SMT process
type Context = SolveEnv SMTContext

data SMTContext = SMTContext
  { ctxPid  :: !ProcessHandle
  , ctxCin  :: !Handle
  , ctxCout :: !Handle
  , ctxLog  :: !(Maybe Handle)
    -- | The handle of the thread writing queries to the SMT solver
  , ctxAsync   :: Async ()
    -- | The next batch of queries to send to the SMT solver
  , ctxTVar    :: TVar Builder
  }

--------------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------------
--------------------------------------------------------------------------------

instance IsSMTContext SMTContext where
  {-# SCC command #-}
  command me !cmd       = say cmd >> hear cmd
    where
      env               = solveSymEnv me
      say               = smtWrite me . Builder.toLazyText . runSmt2 env
      hear CheckSat     = smtRead me
      hear (GetValue _) = smtRead me
      hear _            = return Ok

  asyncCommand me cmd = do
    let env = solveSymEnv me
        cmdText = Builder.toLazyText $ runSmt2 env cmd
    asyncPutStrLn (ctxTVar $ solveSMTContext me) cmdText
    maybe (return ()) (`LTIO.hPutStrLn` cmdText) (ctxLog $ solveSMTContext me)
    where
      asyncPutStrLn :: TVar Builder.Builder -> LT.Text -> IO ()
      asyncPutStrLn tv t = atomically $
        modifyTVar tv (`mappend` (Builder.fromLazyText t `mappend` Builder.fromString "\n"))

  smtRead me = {- SCC "smtRead" #-} do
    when (solveVerbose me) $ LTIO.putStrLn "SMT READ"
    ln  <- smtReadRaw me
    res <- A.parseWith (smtReadRaw me) responseP ln
    case A.eitherResult res of
      Left e  -> Misc.errorstar $ "SMTREAD:" ++ e
      Right r -> do
        maybe (return ()) (\h -> LTIO.hPutStrLn h $ blt ("; SMT Says: " <> (bShow r))) (ctxLog $ solveSMTContext me)
        when (solveVerbose me) $ LTIO.putStrLn $ blt ("SMT Says: " <> bShow r)
        return r

smtExit :: Context -> IO ()
smtExit ctx = smtWrite ctx "(exit)"

smtWrite :: Context -> Raw -> IO ()
smtWrite me !s = smtWriteRaw me s

type SmtParser a = Parser T.Text a

responseP :: SmtParser Response
responseP = {- SCC "responseP" #-} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown

sexpP :: SmtParser Response
sexpP = {- SCC "sexpP" #-} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP

errorP :: SmtParser T.Text
errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP :: SmtParser [(Symbol, T.Text)]
valuesP = A.many1' pairP <* A.char ')'

pairP :: SmtParser (Symbol, T.Text)
pairP = {- SCC "pairP" #-}
  do A.skipSpace
     A.char '('
     !x <- symbolP
     A.skipSpace
     !v <- valueP
     A.char ')'
     return (x,v)

symbolP :: SmtParser Symbol
symbolP = {- SCC "symbolP" #-} symbol <$> A.takeWhile1 (not . isSpace)

valueP :: SmtParser T.Text
valueP = {- SCC "valueP" #-} negativeP
      <|> A.takeWhile1 (\c -> not (c == ')' || isSpace c))

negativeP :: SmtParser T.Text
negativeP
  = do v <- A.char '(' *> A.takeWhile1 (/=')') <* A.char ')'
       return $ "(" <> v <> ")"

smtWriteRaw      :: Context -> Raw -> IO ()
smtWriteRaw me !s = {- SCC "smtWriteRaw" #-} do
  hPutStrLnNow (ctxCout $ solveSMTContext me) s
  maybe (return ()) (`LTIO.hPutStrLn` s) (ctxLog $ solveSMTContext me)

smtReadRaw       :: Context -> IO T.Text
smtReadRaw me    = {- SCC "smtReadRaw" #-} TIO.hGetLine (ctxCin $ solveSMTContext me)
{-# SCC smtReadRaw  #-}

hPutStrLnNow     :: Handle -> LT.Text -> IO ()
hPutStrLnNow h !s = LTIO.hPutStrLn h s >> hFlush h
{-# SCC hPutStrLnNow #-}

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: Config -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext cfg f
  = do me   <- makeProcess cfg
       pre  <- smtPreamble cfg (solver cfg) me
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog <- openFile smtFile WriteMode
       hSetBuffering hLog $ BlockBuffering $ Just $ 1024*1024*64
       let me' = me { solveSMTContext = (solveSMTContext me) { ctxLog = Just hLog }}
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f

withContext :: Config -> FilePath -> (Context -> IO a) -> IO a
withContext cfg f = bracket (makeContext cfg f) cleanupContext

makeContextWithSEnv :: Config -> FilePath -> SymEnv -> (Context -> IO ()) -> IO Context
makeContextWithSEnv cfg f env declare = do
  ctx     <- makeContext cfg f
  let ctx' = ctx { solveSymEnv = env }
  declare ctx'
  return ctx'

withContextWithSEnv
  :: Config -> FilePath -> SymEnv -> (Context -> IO ()) -> (Context -> IO a) -> IO a
withContextWithSEnv cfg f env declare =
  bracket (makeContextWithSEnv cfg f env declare) cleanupContext

makeProcess :: Config -> IO Context
makeProcess cfg
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd (solver cfg)
       loud <- isLoud
       hSetBuffering hOut $ BlockBuffering $ Just $ 1024*1024*64
       hSetBuffering hIn $ BlockBuffering $ Just $ 1024*1024*64
       -- See Note [Async SMT API]
       queueTVar <- newTVarIO mempty
       writerAsync <- async $ forever $ do
         t <- atomically $ do
           builder <- readTVar queueTVar
           let t = Builder.toLazyText builder
           when (LT.null t) retry
           writeTVar queueTVar mempty
           return t
         LTIO.hPutStr hOut t
         hFlush hOut
       return SolveEnv
         { solveVerbose = loud
         , solveSymEnv  = mempty
         , solveSMTContext = SMTContext
             { ctxPid     = pid
             , ctxCin     = hIn
             , ctxCout    = hOut
             , ctxLog     = Nothing
             , ctxAsync   = writerAsync
             , ctxTVar    = queueTVar
             }
         }

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext SolveEnv { solveSMTContext = SMTContext {..} } = do
  cancel ctxAsync
  hCloseMe "ctxCin"  ctxCin
  hCloseMe "ctxCout" ctxCout
  maybe (return ()) (hCloseMe "ctxLog") ctxLog
  waitForProcess ctxPid

hCloseMe :: String -> Handle -> IO ()
hCloseMe msg h = hClose h `catch` (\(exn :: IOException) -> putStrLn $ "OOPS, hClose breaks: " ++ msg ++ show exn)

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

smtCmd         :: SMTSolver -> String --  T.Text
smtCmd Z3      = "z3 -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble :: Config -> SMTSolver -> Context -> IO [LT.Text]
smtPreamble cfg Z3 me
  = do smtWrite me "(get-info :version)"
       v:_ <- T.words . (!!1) . T.splitOn "\"" <$> smtReadRaw me
       checkValidStringFlag Z3 v cfg
       if T.splitOn "." v `versionGreaterEq` ["4", "3", "2"]
         then return $ z3_432_options ++ makeMbqi cfg ++ makeTimeout cfg ++ Thy.preamble cfg Z3
         else return $ z3_options     ++ makeMbqi cfg ++ makeTimeout cfg ++ Thy.preamble cfg Z3
smtPreamble cfg s _
  = checkValidStringFlag s "" cfg >> return (Thy.preamble cfg s)

checkValidStringFlag :: SMTSolver -> T.Text -> Config -> IO ()
checkValidStringFlag smt v cfg
  = when (noString smt v cfg) $
      die $ err dummySpan (text "stringTheory is only supported by z3 version >=4.2.2")

noString :: SMTSolver -> T.Text -> Config -> Bool
noString smt v cfg
  =  stringTheory cfg
  && not (smt == Z3 && (T.splitOn "." v `versionGreaterEq` ["4", "4", "2"]))


versionGreaterEq :: Ord a => [a] -> [a] -> Bool
versionGreaterEq (x:xs) (y:ys)
  | x >  y = True
  | x == y = versionGreaterEq xs ys
  | x <  y = False
versionGreaterEq _  [] = True
versionGreaterEq [] _  = False
versionGreaterEq _ _ = Misc.errorstar "Interface.versionGreater called with bad arguments"

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

makeTimeout :: Config -> [LT.Text]
makeTimeout cfg
  | Just i <- smtTimeout cfg = [ LT.pack ("\n(set-option :timeout " ++ (show i) ++ ")\n")]
  | otherwise                = [""]

makeMbqi :: Config -> [LT.Text]
makeMbqi cfg
  | gradual cfg = [""]
  | otherwise   = ["\n(set-option :smt.mbqi false)"]

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
z3_432_options :: [LT.Text]
z3_432_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model.partial false)"]

z3_options :: [LT.Text]
z3_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model-partial false)"]
