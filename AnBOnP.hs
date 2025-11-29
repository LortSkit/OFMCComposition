{-

Open Source Fixedpoint Model-Checker version 2024

(C) Copyright Sebastian Moedersheim 2003,2024
(C) Copyright Jakub Janaszkiewicz 2022
(C) Copyright Paolo Modesti 2012
(C) Copyright Nicklas Bo Jensen 2012
(C) Copyright IBM Corp. 2009
(C) Copyright ETH Zurich (Swiss Federal Institute of Technology) 2003,2007

All Rights Reserved.

-}

-- | This module defines some types for the parameters and options that the AnB translators use
module AnBOnP where

-- | The output type of the AnB translators
data OutputType
  = -- | Do we use this?
    Internal
  | -- | Do we use this?
    Pretty
  | -- | Just give the abstract syntax tree (for debugging)
    AST
  | -- | standard translation to AVISPA Intermediate Format
    IF
  | -- | output for fixedpoint computation
    FP
  | -- | iterative version of FP (for debugging)
    FPI
  | -- | output for Isabelle
    Isa
  | -- | not implemented
    HLPSL
  | -- | do we use this?
    Amphibian
  | -- | AVANTSSAR output format
    AVANTSSAR
  deriving (Eq, Show)

-- | The version of authentication considered in fixedpoint computation
data Authlevel
  = -- | injective agreement: actually not supported for FP
    Strong
  | -- | standard non-injective agreement
    Weak
  | -- | default; like Weak, but ignore if there are confusions between honest agents
    HWeak
  deriving (Eq, Show)

-- | The set of options and parameters that are passed to the AnB translators
data AnBOptsAndPars
  = AnBOnP
  { -- | AnB file to translate
    anbfilename :: String,
    -- | Algebraic theory file (not supported now)
    theory :: Maybe String,
    -- | Output filename
    anboutput :: Maybe String,
    -- | Number of sessions (for translation to IF)
    numSess :: Maybe Int,
    -- | flag for vertical comp model (either app or ch protocol)
    vert :: Bool,
    -- | max depth of globalcounter when using --vert flag
    maxDepth :: Maybe Int,
    -- | Output type
    outt :: OutputType,
    -- | flag for typed protocol model
    typed :: Bool,
    -- | used?
    iterateFP :: Int,
    -- | authentication model level (for FP/Isa)
    authlevel :: Authlevel,
    -- | whether authentication on oneself is checked
    noowngoal :: Bool,
    -- | rewriting step from IF/Annotated AnB to cryptIF
    if2cif :: Bool
  }

data GoalType = Secc | Auth deriving (Enum, Show, Eq)