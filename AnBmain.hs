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

module AnBmain (newanbmain) where

import AnBOnP
import AnBParser
import Ast
import Data.Maybe
import EnsuranceTools
import FPTranslator
import Lexer
import Translator
import VertTranslator

mkIF :: Protocol -> AnBOptsAndPars -> String
mkIF (protocol@(name, typdec, knowledge, _, actions, goals)) args =
  ( if (vert args)
      then
        let isApp = isAppProtocol actions
            (goaltype, _, _, _) = getGoalTypeAndPayload goals typdec name
            noErrors = not (throwIfVertErrors protocol)
         in if noErrors
              then
                vertruleList (if2cif args) isApp goaltype
                  . vertaddInit isApp goaltype (fromJust (maxDepth args))
                  . vertmakegoals isApp goaltype
                  . vertrulesAddSteps
                  . vertcreateRules isApp goaltype
                  . vertformats
              else error "This is unreachable!"
      else
        ( if (outt args) == IF
            then (\x -> x ++ endstr (noowngoal args)) . ruleList (if2cif args)
            else
              if ((outt args) == FP) || ((outt args) == FPI) || ((outt args) == Isa)
                then ruleListFP [] True
                else error ("Unknown output format: " ++ (show (outt args)))
        )
          . addInit
          . addGoals
          . rulesAddSteps
          . createRules
          . formats
  )
    (mkPTS protocol args)

newanbmain :: String -> AnBOptsAndPars -> String
newanbmain inputstr otp =
  (mkIF (anbparser (alexScanTokens inputstr)) otp)