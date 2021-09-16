{-# LANGUAGE CPP                       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE PatternGuards             #-}

-- | This module contains functions to interact with an SMT solver
module Language.Fixpoint.Smt.Interface (

    -- * Commands
      IsSMTContext (..)
    , Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)

    -- * Query API
    , smtDecl
    , smtDecls
    , smtAssert
    , smtFuncDecl
    , smtAssertAxiom
    , smtCheckUnsat
    , smtCheckSat
    , smtBracket, smtBracketAt
    , smtDistinct
    , smtPush, smtPop
    , smtAssertAsync
    , smtCheckUnsatAsync
    , readCheckUnsat
    , smtBracketAsyncAt
    , smtPushAsync
    , smtPopAsync
    , declare

    -- * Check Validity
    , checkValidWithContext

    ) where

import qualified Language.Fixpoint.Misc          as Misc
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types         hiding (allowHO)
import qualified Language.Fixpoint.Types         as F
import           Language.Fixpoint.Smt.Types
import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Smt.Serialize ()
import           Control.Monad
import           Control.Exception
import qualified Data.HashMap.Strict      as M
import           Data.Maybe              (fromMaybe)
#if !MIN_VERSION_base(4,14,0)
import           Data.Semigroup          (Semigroup (..))
#endif

import qualified Data.Text                as T
import           Language.Fixpoint.SortCheck


-- | This class implements the low level interactions with an SMT solver
class IsSMTContext ctx where
  command :: SolveEnv ctx -> Command -> IO Response
  asyncCommand :: SolveEnv ctx -> Command -> IO ()
  smtRead :: SolveEnv ctx -> IO Response

checkValidWithContext
  :: IsSMTContext ctx => SolveEnv ctx -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValidWithContext me xts p q =
  smtBracket me "checkValidWithContext" $
    checkValid' me xts p q

checkValid' :: IsSMTContext ctx => SolveEnv ctx -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValid' me xts p q = do
  smtDecls me xts
  smtAssert me $ pAnd [p, PNot q]
  smtCheckUnsat me


-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: IsSMTContext ctx => SolveEnv ctx -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop

smtDecls :: IsSMTContext ctx => SolveEnv ctx -> [(Symbol, Sort)] -> IO ()
smtDecls = mapM_ . uncurry . smtDecl

smtDecl :: IsSMTContext ctx => SolveEnv ctx -> Symbol -> Sort -> IO ()
smtDecl me x t = interact' me ({- notracepp msg $ -} Declare (symbolSafeText x) ins' out')
  where
    ins'       = sortSmtSort False env <$> ins
    out'       = sortSmtSort False env     out
    (ins, out) = deconSort t
    _msg        = "smtDecl: " ++ showpp (x, t, ins, out)
    env        = seData (solveSymEnv me)

smtFuncDecl :: IsSMTContext ctx => SolveEnv ctx -> T.Text -> ([SmtSort],  SmtSort) -> IO ()
smtFuncDecl me x (ts, t) = interact' me (Declare x ts t)

smtDataDecl :: IsSMTContext ctx => SolveEnv ctx -> [DataDecl] -> IO ()
smtDataDecl me ds = interact' me (DeclData ds)

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([] , t  )

-- hack now this is used only for checking gradual condition.
smtCheckSat :: IsSMTContext ctx => SolveEnv ctx -> Expr -> IO Bool
smtCheckSat me p
 = smtAssert me p >> (ans <$> command me CheckSat)
 where
   ans Sat = True
   ans _   = False

smtAssert :: IsSMTContext ctx => SolveEnv ctx -> Expr -> IO ()
smtAssert me p  = interact' me (Assert Nothing p)

readCheckUnsat :: IsSMTContext ctx => SolveEnv ctx -> IO Bool
readCheckUnsat me = respSat <$> smtRead me

-----------------------------------------------------------------
-- Async calls to the smt
--
-- See Note [Async SMT API]
-----------------------------------------------------------------

smtAssertAsync :: IsSMTContext ctx => SolveEnv ctx -> Expr -> IO ()
smtAssertAsync me p  = asyncCommand me $ Assert Nothing p

smtCheckUnsatAsync :: IsSMTContext ctx => SolveEnv ctx -> IO ()
smtCheckUnsatAsync me = asyncCommand me CheckSat

smtBracketAsyncAt :: IsSMTContext ctx => SrcSpan -> SolveEnv ctx -> String -> IO a -> IO a
smtBracketAsyncAt sp x y z = smtBracketAsync x y z `catch` dieAt sp

smtBracketAsync :: IsSMTContext ctx => SolveEnv ctx -> String -> IO a -> IO a
smtBracketAsync me _msg a   = do
  smtPushAsync me
  r <- a
  smtPopAsync me
  return r

smtPushAsync, smtPopAsync :: IsSMTContext ctx => SolveEnv ctx -> IO ()
smtPushAsync me = asyncCommand me Push
smtPopAsync me = asyncCommand me Pop

-----------------------------------------------------------------

smtAssertAxiom :: IsSMTContext ctx => SolveEnv ctx -> Triggered Expr -> IO ()
smtAssertAxiom me p  = interact' me (AssertAx p)

smtDistinct :: IsSMTContext ctx => SolveEnv ctx -> [Expr] -> IO ()
smtDistinct me az = interact' me (Distinct az)

smtCheckUnsat :: IsSMTContext ctx => SolveEnv ctx -> IO Bool
smtCheckUnsat me  = respSat <$> command me CheckSat

smtBracketAt :: IsSMTContext ctx => SrcSpan -> SolveEnv ctx -> String -> IO a -> IO a
smtBracketAt sp x y z = smtBracket x y z `catch` dieAt sp

smtBracket :: IsSMTContext ctx => SolveEnv ctx -> String -> IO a -> IO a
smtBracket me _msg a   = do
  smtPush me
  r <- a
  smtPop me
  return r

interact' :: IsSMTContext ctx => SolveEnv ctx -> Command -> IO ()
interact' me cmd  = void $ command me cmd


--------------------------------------------------------------------------------
declare :: IsSMTContext ctx => SolveEnv ctx -> IO () -- SolveM ()
--------------------------------------------------------------------------------
declare me = do
  forM_ dss    $           smtDataDecl me
  forM_ thyXTs $ uncurry $ smtDecl     me
  forM_ qryXTs $ uncurry $ smtDecl     me
  forM_ ats    $ uncurry $ smtFuncDecl me
  forM_ ess    $           smtDistinct me
  forM_ axs    $           smtAssert   me
  where
    env        = solveSymEnv me
    dss        = dataDeclarations          env
    lts        = F.toListSEnv . F.seLits $ env
    ess        = distinctLiterals  lts
    axs        = Thy.axiomLiterals lts
    thyXTs     =                    filter (isKind 1) xts
    qryXTs     = Misc.mapSnd tx <$> filter (isKind 2) xts
    isKind n   = (n ==)  . symKind env . fst
    xts        = {- tracepp "symbolSorts" $ -} symbolSorts (F.seSort env) 
    tx         = elaborate    "declare" env
    ats        = funcSortVars env

symbolSorts :: F.SEnv F.Sort -> [(F.Symbol, F.Sort)]
symbolSorts env = [(x, tx t) | (x, t) <- F.toListSEnv env ]
 where
  tx t@(FObj a) = fromMaybe t (F.lookupSEnv a env)
  tx t          = t

dataDeclarations :: SymEnv -> [[DataDecl]]
dataDeclarations = orderDeclarations . map snd . F.toListSEnv . F.seData

funcSortVars :: F.SymEnv -> [(T.Text, ([F.SmtSort], F.SmtSort))]
funcSortVars env  = [(var applyName  t       , appSort t) | t <- ts]
                 ++ [(var coerceName t       , ([t1],t2)) | t@(t1, t2) <- ts]
                 ++ [(var lambdaName t       , lamSort t) | t <- ts]
                 ++ [(var (lamArgSymbol i) t , argSort t) | t@(_,F.SInt) <- ts, i <- [1..Thy.maxLamArg] ]
  where
    var n         = F.symbolAtSmtName n env ()
    ts            = M.keys (F.seAppls env)
    appSort (s,t) = ([F.SInt, s], t)
    lamSort (s,t) = ([s, t], F.SInt)
    argSort (s,_) = ([]    , s)

-- | 'symKind' returns {0, 1, 2} where:
--   0 = Theory-Definition,
--   1 = Theory-Declaration,
--   2 = Query-Binder

symKind :: F.SymEnv -> F.Symbol -> Int
symKind env x = case F.tsInterp <$> F.symEnvTheory x env of
                  Just F.Theory   -> 0
                  Just F.Ctor     -> 0
                  Just F.Test     -> 0
                  Just F.Field    -> 0
                  Just F.Uninterp -> 1
                  Nothing         -> 2
              -- Just t  -> if tsInterp t then 0 else 1


-- assumes :: [F.Expr] -> SolveM ()
-- assumes es = withContext $ \me -> forM_  es $ smtAssert me

-- | `distinctLiterals` is used solely to determine the set of literals
--   (of each sort) that are *disequal* to each other, e.g. EQ, LT, GT,
--   or string literals "cat", "dog", "mouse". These should only include
--   non-function sorted values.
distinctLiterals :: [(F.Symbol, F.Sort)] -> [[F.Expr]]
distinctLiterals xts = [ es | (_, es) <- tess ]
   where
    tess             = Misc.groupList [(t, F.expr x) | (x, t) <- xts, notFun t]
    notFun           = not . F.isFunctionSortedReft . (`F.RR` F.trueReft)
    -- _notStr          = not . (F.strSort ==) . F.sr_sort . (`F.RR` F.trueReft)

