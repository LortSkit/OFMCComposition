module EnsuranceTools where

import AnBOnP
import Ast

isAppProtocol :: Actions -> Bool
isAppProtocol [] = False
isAppProtocol (a : as) =
  let ((_, channeltype, _), _, _, _) = a
   in case channeltype of
        ChannelProtocol _ -> True
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

throwIfVertErrors :: Protocol -> Bool
-- throwIfVertErrors protocol@(_, _, _, _, actions, goals) | trace ("isApp: " ++ show (isAppProtocol actions) ++ ", length of actions: " ++ show (length actions)) False = undefined
throwIfVertErrors protocol@(name, _, _, _, actions, goals) =
  let isApp = isAppProtocol actions
      (isCompliant, numActions) = if isApp then isAppCompliant actions else isChCompliant actions
      protocolType = if isApp then "App" else "Ch"
      expectedNumActions = if isApp then 2 else 1
      goaltypececk = getGoalType goals /= Conf -- Will throw error in getGoalType if it's not Auth or Secc, but is used below to avoid it being overlook by haskell lazy evaluation
      hascompliancyissues =
        if not isCompliant
          then error ("Protocol is not compliant with " ++ protocolType ++ " protocol: Protocol has " ++ show numActions ++ " actions, expected " ++ show expectedNumActions)
          else False

      extractChannelNameFromActions :: Action -> String
      extractChannelNameFromActions action =
        case action of
          ((sp@(_, _, _), ChannelProtocol id, _), _, _, _) -> id
          _ -> error "Unexpectedly got an Ch protcol - Was expecting an App protocol"

      hasChannelNameErrors :: Actions -> String -> Bool
      hasChannelNameErrors actions protname
        | hascompliancyissues = error "Unreachable!1"
        | otherwise = case actions of
            [action1, action2] ->
              let id1 = extractChannelNameFromActions action1
                  id2 = extractChannelNameFromActions action2
               in if id1 /= id2
                    then error ("App protocol may not use two different channel protocols! Please make sure -" ++ id1 ++ "-> matches with -" ++ id2 ++ "->")
                    else
                      if id1 == protname
                        then error ("Disallowed use of -" ++ id1 ++ "->: The channel protocol used may not share name with the app protocol!")
                        else False
            _ -> error "Unreachable!2"
      haschannelnameerrors = if isApp then hasChannelNameErrors actions name else False
   in (not (not hascompliancyissues && not haschannelnameerrors && goaltypececk) && error "Unreachable!3")