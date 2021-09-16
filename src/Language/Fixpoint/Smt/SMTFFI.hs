{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE QuasiQuotes               #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE ScopedTypeVariables       #-}

-- | This module implements an interface to smt solvers via FFI
module Language.Fixpoint.Smt.SMTFFI
  ( SMTContext
  ) where

import Control.Exception (bracket)
import Foreign.Ptr
import qualified Language.C.Inline.Cpp as C
import qualified Language.C.Inline.Cpp.Exceptions as C
import qualified Language.C.Inline.Unsafe as CU
import Language.Haskell.TH.Syntax
import qualified Language.Fixpoint.Misc          as Misc
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Types         hiding (Sort, allowHO)
import qualified Language.Fixpoint.Types         as F
import           Language.Fixpoint.Smt.Interface (IsSMTContext(..))
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Serialize ()
import           Control.Monad
import           Data.Text.Encoding as Text


data SMTContext = SMTContext
  { ctxSolver :: Ptr SmtSolver
  }

type Context = SolveEnv SMTContext

contextSolver :: Context -> Ptr SmtSolver
contextSolver = ctxSolver . solveSMTContext

data Term
data Sort
data SmtSolver
data DatatypeDecl
data DatatypeConstructorDecl

C.context $ C.cppCtx <> C.bsCtx <>
  C.cppTypePairs
    [ ("SmtSolver", [t| SmtSolver |])
    , ("DatatypeDecl", [t| DatatypeDecl |])
    , ("DatatypeConstructorDecl", [t| DatatypeConstructorDecl |])
    , ("Sort", [t| Sort |])
    , ("Term", [t| Term |])
    ]

C.include "smt.h"
C.include "z3_factory.h"
C.include "z3_sort.h"

C.using "namespace smt"
C.using "namespace std"

-- | This class implements the low level interactions with an SMT solver
instance IsSMTContext SMTContext where
  command ctx =
    \case
    Push -> do
      [CU.exp| void { (*$(SmtSolver* solver))->push(1) } |]
      return Ok
    Pop -> do
      [CU.exp| void { (*$(SmtSolver* solver))->pop(1) } |]
      return Ok
    CheckSat -> do
      r <- [CU.exp| int { (*$(SmtSolver* solver))->check_sat().result } |]
      if r == [CU.pure| int { SAT } |] then return Sat
        else if r == [CU.pure| int { UNSAT } |] then return Unsat
        else return Unknown
    DeclData xs -> do
      mapM_ (makeDatatypeDecl ctx) xs
      return Ok
    _ ->
      error "unimplemented"
    where
      solver = contextSolver ctx

makeDatatypeDecl :: Context -> DataDecl -> IO ()
makeDatatypeDecl ctx (DDecl ftycon nvars dcs) = do
  let solver = contextSolver ctx
      bsName = Text.encodeUtf8 $ symbolText (symbol ftycon)
  bracket [CU.exp| DatatypeDecl* {
      new DatatypeDecl((*$(SmtSolver* solver))->make_datatype_decl(string($bs-ptr:bsName, $bs-len:bsName)))
    } |]
    (\dd -> [CU.exp| void { delete $(DatatypeDecl* dd) } |])
    $ \dd ->
      mapM_ (addDataConstructorDecl ctx dd) dcs

addDataConstructorDecl :: Context -> Ptr DatatypeDecl -> DataCtor -> IO ()
addDataConstructorDecl ctx dd (DCtor lsym dfs) = do
  let solver = contextSolver ctx
      bsName = Text.encodeUtf8 $ symbolText (val lsym)
  bracket [CU.exp| DatatypeConstructorDecl* {
      new DatatypeConstructorDecl((*$(SmtSolver* solver))->make_datatype_constructor_decl(string($bs-ptr:bsName, $bs-len:bsName)))
    } |]
    (\dc -> [CU.exp| void { delete $(DatatypeConstructorDecl* dc) } |])
    $ \dc -> do
      mapM_ (addDataField ctx dc) dfs
      [CU.block| void {
        (*$(SmtSolver* solver))->add_constructor(*$(DatatypeDecl* dd), *$(DatatypeConstructorDecl* dc));
        } |]

addDataField :: Context -> Ptr DatatypeConstructorDecl -> DataField -> IO ()
addDataField ctx dc (DField lsym sr) = do
  let solver = contextSolver ctx
      bsName = Text.encodeUtf8 $ symbolText (val lsym)
  bracket
    (makeSort ctx sr)
    (\srPtr -> [CU.exp| void { delete $(Sort* srPtr) } |])
    $ \srPtr ->
      [CU.block| void {
          (*$(SmtSolver* solver))->add_selector(
              *$(DatatypeConstructorDecl* dc),
              string($bs-ptr:bsName, $bs-len:bsName),
              *$(Sort* srPtr));
        } |]

makeSort :: Context -> F.Sort -> IO (Ptr Sort)
makeSort ctx sr = case sortSmtSort True (seData env) sr of
  SInt ->
    [CU.exp| Sort* { new Sort((*$(SmtSolver* solver))->make_sort(INT)) } |]
  SReal ->
    [CU.exp| Sort* { new Sort((*$(SmtSolver* solver))->make_sort(REAL)) } |]
  SBool ->
    [CU.exp| Sort* { new Sort((*$(SmtSolver* solver))->make_sort(BOOL)) } |]
  _ -> undefined
  where
    solver = contextSolver ctx
    env = solveSymEnv ctx

{-

data Sort = FInt
          | FReal
          | FNum                 -- ^ numeric kind for Num tyvars
          | FFrac                -- ^ numeric kind for Fractional tyvars
          | FObj  !Symbol        -- ^ uninterpreted type
          | FVar  !Int           -- ^ fixpoint type variable
          | FFunc !Sort !Sort    -- ^ function
          | FAbs  !Int !Sort     -- ^ type-abstraction
          | FTC   !FTycon
          | FApp  !Sort !Sort    -- ^ constructed type
            deriving (Eq, Ord, Show, Data, Typeable, Generic)



-- | Commands issued to SMT engine
data Command      = Push
                  | Pop
                  | CheckSat
                  | DeclData ![DataDecl]
                  | Declare  !Symbol [SmtSort] !SmtSort
                  | Define   !Sort
                  | Assert   !(Maybe Int) !Expr
                  | AssertAx !(Triggered Expr)
                  | Distinct [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue [Symbol]
                  | CMany    [Command]
                  deriving (Eq, Show)

data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, T.Text)]
                  | Error !T.Text
                  deriving (Eq, Show)

data DataField = DField
  { dfName :: !LocSymbol          -- ^ Field Name
  , dfSort :: !Sort               -- ^ Field Sort
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataCtor = DCtor
  { dcName   :: !LocSymbol        -- ^ Ctor Name
  , dcFields :: ![DataField]      -- ^ Ctor Fields
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)

data DataDecl = DDecl
  { ddTyCon :: !FTycon            -- ^ Name of defined datatype
  , ddVars  :: !Int               -- ^ Number of type variables
  , ddCtors :: [DataCtor]         -- ^ Datatype Ctors. Invariant: type variables bound in ctors are greater than ddVars
  } deriving (Eq, Ord, Show, Data, Typeable, Generic)


-}

