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
import FPTranslator
import Lexer
import Msg
import ProtocolTranslationTypes
import Translator
import VertTranslator

mkIF :: Protocol -> AnBOptsAndPars -> String
mkIF (protocol@(_, typdec, knowledge, _, actions, _)) args =
  ( if (vert args)
      then
        let isApp = isAppProtocol actions
            (errVar, numActions) = if isApp then isAppCompliant actions else isChCompliant actions
            protocolType = if isApp then "App" else "Ch"
            expectedNumActions = if isApp then 2 else 1
         in if not errVar then error ("Protocol is not compliant with " ++ protocolType ++ " protocol: Protocol has " ++ show numActions ++ " actions, expected " ++ show expectedNumActions) else vertruleList (if2cif args) isApp . vertmakegoals isApp . vertaddInit isApp (fromJust (maxDepth args)) . vertrulesAddSteps . vertcreateRules isApp . vertformats
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

isAppProtocol :: Actions -> Bool
isAppProtocol [] = False
isAppProtocol (a : as) =
  let ((_, channeltype, _), _, _, _) = a
   in case channeltype of
        ChannelProtocol -> True
        _ -> isAppProtocol as

isAppCompliant :: Actions -> (Bool, Int)
isAppCompliant actions = (length actions == 2, length actions)

isChCompliant :: Actions -> (Bool, Int)
isChCompliant actions = (length actions == 1, length actions)

newanbmain :: String -> AnBOptsAndPars -> String
newanbmain inputstr otp =
  (mkIF (anbparser (alexScanTokens inputstr)) otp)