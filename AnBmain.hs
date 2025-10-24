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
import FPTranslator
import Lexer
import Msg
import ProtocolTranslationTypes
import Translator
import VertTranslator

mkIF :: Protocol -> AnBOptsAndPars -> String
mkIF (protocol@(_, typdec, knowledge, _, actions, _)) args =
  ( if (vert args)
      then (\x -> x ++ vertendstr (noowngoal args)) . vertruleList (if2cif args) (isAppProtocol actions) . vertaddInit (isAppProtocol actions) . vertrulesAddSteps . vertcreateRules (isAppProtocol actions) . vertformats
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

newanbmain inputstr otp =
  (mkIF (anbparser (alexScanTokens inputstr)) otp)