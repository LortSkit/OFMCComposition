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
mkIF (protocol@(_, typdec, knowledge, _, actions, goals)) args =
  ( if (vert args)
      then
        let isApp = isAppProtocol actions
            (isCompliant, numActions) = if isApp then isAppCompliant actions else isChCompliant actions
            protocolType = if isApp then "App" else "Ch"
            expectedNumActions = if isApp then 2 else 1
            goaltype = getGoalType goals
            isImplemented = not ((not isApp) && goaltype == Auth)
         in if not isCompliant
              then error ("Protocol is not compliant with " ++ protocolType ++ " protocol: Protocol has " ++ show numActions ++ " actions, expected " ++ show expectedNumActions)
              else
                if not isImplemented
                  then error "Chauth has not been proven or implemented yet!"
                  else vertruleList (if2cif args) isApp goaltype . vertmakegoals isApp goaltype . vertaddInit isApp goaltype (fromJust (maxDepth args)) . vertrulesAddSteps . vertcreateRules isApp goaltype . vertformats
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

getGoalType :: Goals -> GoalType
getGoalType goals =
  let numberOfGoals = length goals
      isGoalCompliant = numberOfGoals == 1
   in if not isGoalCompliant
        then error ("Protocol does not have the correct number of goals! Got " ++ show numberOfGoals ++ " goals, expected 1.")
        else case head goals of
          ChGoal channel msg ->
            let (_, channeltype, _) = channel
             in case channeltype of
                  FreshAuthentic -> Auth
                  FreshSecure -> Secc
                  Confidential -> error "Confidential goaltype is not supported! Please use either *-> or *->*."
          x -> error ("Protocol has the wrong goaltype " ++ show x ++ "!\nExpected ((AGENT1,False,Nothing),X,(AGENT2,False,Nothing)), where X = FreshSecure, FreshAuthentic")

newanbmain :: String -> AnBOptsAndPars -> String
newanbmain inputstr otp =
  (mkIF (anbparser (alexScanTokens inputstr)) otp)