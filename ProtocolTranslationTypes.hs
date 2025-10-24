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
-- Alexander Laukamp created this file, though most things are taken from Translator.hs

module ProtocolTranslationTypes where

import AnBOnP
import Ast
import Data.List
import LMsg
import Msg
import MsgPat

data Fact
  = State Ident [LMsg]
  | FPState Ident [Msg]
  | Iknows Msg
  | Fact Ident [Msg]
  deriving (Eq, Show)

type Rule = ([Fact], Eqs, [Ident], [Fact])

lhs (l, _, _) = l

rhs (_, _, r) = r

frv (_, f, _) = f

identsF :: Fact -> [Ident]
identsF (State _ msgs) = error "identsf of state"
identsF (FPState _ msgs) = nub (concatMap idents msgs)
identsF (Iknows msg) = nub (idents msg)
identsF (Fact _ msgs) = nub (concatMap idents msgs)

identsFL m = nub (concatMap identsF m)

type Rule' = (Rule, ProtocolState, ProtocolState)

type Eqs = [(Msg, Msg)]

type Role = (Ident, [Rule'])

data ProtocolTranslationState = PTS
  { protocol :: Protocol,
    options :: AnBOptsAndPars,
    roles :: [Role],
    rules :: [Rule],
    initial :: String,
    goals :: String
  }

mkPTS :: Protocol -> AnBOptsAndPars -> ProtocolTranslationState
mkPTS protocol options = PTS {protocol = protocol, options = options, roles = [], rules = [], initial = "", goals = ""}