------------------------ MODULE Enviroment -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxChannelID, MaxPortID, MaxVersion, MaxConnectionID

VARIABLES chainAStore, chainBStore

vars == <<chainAStore, chainBStore>>

chainStores == <<chainAStore, chainBStore>>

chainAvars == <<chainAStore>>

chainBvars == <<chainBStore>>

\*client
nullHeight == 0
nullClientID == 0

\*connection
nullConnectionID == 0
ConnectionIDs == 1..MaxConnectionID

nullConnectionEnd == 
    [
        state |-> "UNINIT",
        connectionID |-> nullConnectionID,
        clientID |-> nullClientID,
        counterpartyConnectionID |-> nullConnectionID,
        counterpartyClientID |-> nullClientID,
        versions |-> {}
    ]

\*port
nullPortID == 0
PortIDs == 1..MaxPortID

\* channel
Versions == 1..MaxVersion
nullOrdering == "none"
nullVersion == 0
nullChannelID == 0

ChannelIDs == 1..MaxChannelID
ChannelStates == {"UNINIT","INIT","TRYOPEN","OPEN","CLOSED"}
Orders == {"UNORDERED","ORDERED","ORDERED_ALLOW_TIMEOUT"}

nullChannelEnd == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        state |-> "UNINIT",
        order |-> nullOrdering,
        counterpartyPortID |-> nullPortID,
        counterpartyChannelID |-> nullChannelID,
        connectionID |-> nullConnectionID,
        version |-> nullVersion
    ]
  
\* chain
ChainIDs == {"chainA", "chainB"}

ChainA == INSTANCE Chain 
            WITH chainID <- "chainA",
                counterpartyChainID <- "chainB",
                chainStore <- chainAStore

ChainB == INSTANCE Chain 
            WITH chainID <- "chainB",
                counterpartyChainID <- "chainA",
                chainStore <- chainBStore
                
getChainStore(chainID) == 
    IF chainID = "chainA"
    THEN chainAStore
    ELSE chainBStore
        
getCounterpartyChainID(chainID) ==
    IF chainID = "chainA"
    THEN "chainB"
    ELSE "chainA"

getChannelEnd(chainID, portID, channelID) ==
    LET chainstore == getChainStore(chainID)
        channelEnds == chainstore.channelEnds IN 
    IF channelID \in DOMAIN channelEnds /\ channelEnds[channelID].portID = portID
    THEN channelEnds[channelID]
    ELSE nullChannelEnd

proofChannelState(chainID, portID, channelID) ==
    LET chainstore == getChainStore(chainID)
        channels == chainstore.channelEnds
    IN
    IF channelID \in DOMAIN channels /\ channels[channelID].portID = portID
    THEN [chainID |-> chainID, channel |-> channels[channelID]]
    ELSE [chainID |-> chainID, channel |-> nullChannelEnd]

HandleChannel(chainID) ==
    \E order \in Orders, connectionID \in ConnectionIDs, 
        portID, counterpartyPortID \in PortIDs, channelID, counterpartyChannelID \in ChannelIDs, version, counterpartyVersion \in Versions: 
        LET 
            counterpartyChainID == getCounterpartyChainID(chainID)
            proof == proofChannelState(counterpartyChainID, counterpartyPortID, counterpartyChannelID) 
        IN
        IF chainID = "chainA"
        THEN  
            /\ ChainA!HandleChannel(order, connectionID, portID, channelID, counterpartyPortID, counterpartyChannelID, version, counterpartyVersion, proof)
            /\ UNCHANGED chainBvars
        ELSE  
            /\ ChainB!HandleChannel(order, connectionID, portID, channelID, counterpartyPortID, counterpartyChannelID, version, counterpartyVersion, proof)
            /\ UNCHANGED chainAvars

Init == 
    /\ ChainA!Init
    /\ ChainB!Init

Next == 
        \/ \E chainID \in ChainIDs: 
            \/ HandleChannel(chainID)
        \/ UNCHANGED vars

Fairness == 
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK == 
    /\ ChainA!TypeOK
    /\ ChainB!TypeOK

SafaConnInit == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    [](channelEnd.state = "INIT" 
                        => ~(<> (channelEnd.state =  "UNINIT")))


SafaConnTry == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    [](channelEnd.state = "TRYOPEN" 
                        => ~(<> (channelEnd.state =  "UNINIT" 
                                \/ channelEnd.state =  "INIT")))


SafaConnOpen1 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    [](channelEnd.state = "OPEN" 
                        => ~(<> (channelEnd.state =  "UNINIT" 
                                \/ channelEnd.state =  "INIT"
                                \/ channelEnd.state =  "TRYOPEN")))

SafeConnOpen2 == [] [\A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    \/ channelEnd'.state = channelEnd.state
                    \/ channelEnd'.state = "OPEN" => (channelEnd.state = "INIT" \/ channelEnd.state = "TRYOPEN")]_vars

SafaConnClose1 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    [](channelEnd.state = "CLOSED" 
                        => ~(<> (channelEnd.state =  "UNINIT" 
                                \/ channelEnd.state =  "INIT"
                                \/ channelEnd.state =  "TRYOPEN"
                                \/ channelEnd.state = "OPEN")))

SafeConnClose2 == [] [\A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    \/ channelEnd'.state = channelEnd.state
                    \/ channelEnd'.state = "CLOSED" => (channelEnd.state = "INIT" \/ channelEnd.state = "TRYOPEN" \/ channelEnd.state = "OPEN")]_vars

SafeHandShake == /\ SafaConnInit
                 /\ SafaConnTry
                 /\ SafaConnOpen1
                 /\ SafeConnOpen2
                 /\ SafaConnClose1
                 /\ SafeConnClose2

LiveConnInit == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    <> (channelEnd.state = "INIT" \/ channelEnd.state = "TRYOPEN")

LiveConnOpen1 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                    <> (channelEnd.state = "OPEN")

LiveConnOpen2 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                   <>(channelEnd.state = "TRYOPEN" /\ counterpartyChannelEnd.state = "INIT")
                        => <>(channelEnd.state = "OPEN")

LiveConnClose == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID) IN
                   <> [] (channelEnd.state = "CLOSED")

LiveHandShake == /\ LiveConnInit
                 \*/\ LiveConnOpen1
                 \*/\ LiveConnOpen2
                 /\ LiveConnClose

CorrectOpen1== \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                    [] ( channelEnd.state = "OPEN" => <> (counterpartyChannelEnd.state = "OPEN" \/ counterpartyChannelEnd.state = "CLOSED"))

CorrectOpen2== \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                     <> (channelEnd.state = "OPEN") => <> (counterpartyChannelEnd.state = "OPEN" \/ counterpartyChannelEnd.state = "CLOSED") 
                          

CorrectVersion1 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                    [] (channelEnd.state = "OPEN" => <> (counterpartyChannelEnd.version = channelEnd.version))

CorrectVersion2 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                    <> (channelEnd.state = "OPEN") => <> (counterpartyChannelEnd.version = channelEnd.version) 

CorrectOrder1 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                    [] (channelEnd.state = "OPEN" => <> (counterpartyChannelEnd.order = channelEnd.order))

CorrectOrder2 == \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                    <> (channelEnd.state = "OPEN") => <> (counterpartyChannelEnd.order = channelEnd.order) 

(*
CorrectClose1== \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                    [] ((channelEnd.state = "CLOSED" /\ channelEnd.counterpartyChannelID /= nullChannelID) => <> (counterpartyChannelEnd.state = "CLOSED"))

CorrectClose2== \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
                    LET channelEnd == getChannelEnd(chainID, portID, channelID)
                        counterpartyChainID == getCounterpartyChainID(chainID)
                        counterpartyChannelEnd == 
                                getChannelEnd(counterpartyChainID, channelEnd.counterpartyPortID, channelEnd.counterpartyChannelID) IN
                     <> ((channelEnd.state = "CLOSED" /\ channelEnd.counterpartyChannelID /= nullChannelID)) => <> (counterpartyChannelEnd.state = "CLOSED") 
*)

CorrectHandShake == /\ CorrectOpen1
                    /\ CorrectOpen2
                    /\ CorrectVersion1
                    /\ CorrectVersion2
                    /\ CorrectOrder1
                    /\ CorrectOrder2
                    \*/\ CorrectClose1
                    \*/\ CorrectClose2    
=============================================================================