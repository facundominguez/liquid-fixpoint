{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Smt.Types (

    -- * Serialized Representation
    --    symbolBuilder

    -- * Commands
      Command  (..)

    -- * Responses
    , Response (..)
    , respSat

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)
    , runSmt2

    -- * SMTLIB2 Process Context
    , Context
    , SMTContext (..)
    , SolveEnv (..)

    ) where

import           Control.Concurrent.Async (Async)
import           Control.Concurrent.STM (TVar)
import           Language.Fixpoint.Types
import           Language.Fixpoint.Utils.Builder (Builder)
import qualified Data.Text                as T
import           Text.PrettyPrint.HughesPJ

import           System.IO                (Handle)
import           System.Process
-- import           Language.Fixpoint.Misc   (traceShow)

--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------

-- symbolBuilder :: Symbol -> LT.Builder
-- symbolBuilder = LT.fromText . symbolSafeText

-- | Commands issued to SMT engine
data Command      = Push
                  | Pop
                  | CheckSat
                  | DeclData ![DataDecl]
                  | Declare  T.Text [SmtSort] !SmtSort
                  | Define   !Sort
                  | Assert   !(Maybe Int) !Expr
                  | AssertAx !(Triggered Expr)
                  | Distinct [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue [Symbol]
                  | CMany    [Command]
                  deriving (Eq, Show)

instance PPrint Command where
  pprintTidy _ = ppCmd

ppCmd :: Command -> Doc
ppCmd Push             = text "Push"
ppCmd Pop              = text "Pop"
ppCmd CheckSat         = text "CheckSat"
ppCmd (DeclData d)     = text "Data" <+> pprint d
ppCmd (Declare x [] t) = text "Declare" <+> text (T.unpack x) <+> text ":" <+> pprint t
ppCmd (Declare x ts t) = text "Declare" <+> text (T.unpack x) <+> text ":" <+> parens (pprint ts) <+> pprint t
ppCmd (Define {})   = text "Define ..."
ppCmd (Assert _ e)  = text "Assert" <+> pprint e
ppCmd (AssertAx _)  = text "AssertAxiom ..."
ppCmd (Distinct {}) = text "Distinct ..."
ppCmd (GetValue {}) = text "GetValue ..."
ppCmd (CMany {})    = text "CMany ..."

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, T.Text)]
                  | Error !T.Text
                  deriving (Eq, Show)

respSat :: Response -> Bool
respSat Unsat   = True
respSat Sat     = False
respSat Unknown = False
respSat r       = die $ err dummySpan $ text ("crash: SMTLIB2 respSat = " ++ show r)

-- | Information about the external SMT process
type Context = SolveEnv SMTContext

data SolveEnv c = SolveEnv
  { solveVerbose    :: !Bool
  , solveSymEnv     :: !SymEnv
  , solveSMTContext :: c
  }

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
-- | AST Conversion: Types that can be serialized ------------------------------
--------------------------------------------------------------------------------

class SMTLIB2 a where
  smt2 :: SymEnv -> a -> Builder

runSmt2 :: (SMTLIB2 a) => SymEnv -> a -> Builder
runSmt2 = smt2
