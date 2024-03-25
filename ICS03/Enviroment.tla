------------------------ MODULE Enviroment -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxConnectionID, MaxVersion

VARIABLES chainAStore, chainBStore

vars == <<chainAStore, chainBStore>>

chainStores == <<chainAStore, chainBStore>>

chainAvars == <<chainAStore>>

chainBvars == <<chainBStore>>

ChainIDs == {"chainA", "chainB"}
ClientIDs == {"clA","clB"}
ConnectionIDs == 1..MaxConnectionID
Versions == 1..MaxVersion
ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

nullClientID == "none"
nullConnectionID == 0

nullConnectionEnd == 
    [
        state |-> "UNINIT",
        connectionID |-> nullConnectionID,
        clientID |-> nullClientID,
        counterpartyConnectionID |-> nullConnectionID,
        counterpartyClientID |-> nullClientID,
        versions |-> {}
    ]

ConnectionEnds == 
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyClientID : ClientIDs \union {nullClientID},
        versions : SUBSET Versions
    ]

ChainA == INSTANCE Chain 
            WITH chainID <- "chainA",
                counterpartyChainID <- "chainB",
                ClientID <- "clA",
                chainStore <- chainAStore

ChainB == INSTANCE Chain 
            WITH chainID <- "chainB",
                counterpartyChainID <- "chainA",
                ClientID <- "clB",
                chainStore <- chainBStore

getChainStore(chainID) == 
    IF chainID = "chainA"
    THEN chainAStore
    ELSE chainBStore

getCounterpartyClientID(clientID) ==
    IF clientID = "clA"
    THEN "clB"
    ELSE "clA"

getCounterpartyChainID(chainID) ==
    IF chainID = "chainA"
    THEN "chainB"
    ELSE "chainA"

getConnectionEnd(chainID, connectionID) ==
    LET chainstore == getChainStore(chainID)
        connectionEnds == chainstore.connectionEnds IN 
    IF connectionID \in DOMAIN connectionEnds
    THEN connectionEnds[connectionID]
    ELSE nullConnectionEnd

proofConnectionState(chainID, connectionID) ==
    LET chainstore == getChainStore(chainID)
        connectionEnds == chainstore.connectionEnds
    IN
    IF connectionID \in DOMAIN connectionEnds
    THEN [chainID |-> chainID, connection |-> connectionEnds[connectionID]]
    ELSE [chainID |-> chainID, connection |-> nullConnectionEnd]

HandleConnection(chainID) ==
    \E clientID\in ClientIDs, connectionID, counterpartyConnectionID \in ConnectionIDs, version \in (SUBSET Versions \ {{}}): 
        LET 
            counterpartyClientID == getCounterpartyClientID(clientID)
            counterpartyChainID == getCounterpartyChainID(chainID)
            proof == proofConnectionState(counterpartyChainID, counterpartyConnectionID) 
        IN
        IF chainID = "chainA"
        THEN  
            /\ ChainA!HandleChannel(clientID, counterpartyClientID, connectionID, counterpartyConnectionID, version, proof)
            /\ UNCHANGED chainBvars
        ELSE  
            /\ ChainB!HandleChannel(clientID, counterpartyClientID, connectionID, counterpartyConnectionID, version, proof)
            /\ UNCHANGED chainAvars

Init == 
    /\ ChainA!Init(Versions)
    /\ ChainB!Init(Versions)

Next == 
        \/ \E chainID \in ChainIDs: 
            \/ HandleConnection(chainID)
        \/ UNCHANGED vars

Fairness == 
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness


TypeOK == 
    /\ 
        \A chainID \in ChainIDs:
        LET chainStore == getChainStore(chainID) IN
        \A connectionID \in DOMAIN chainStore.connectionEnds : chainStore.connectionEnds[connectionID] \in ConnectionEnds

SafeHandShake1 == [] [\A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connection == getConnectionEnd(chainID, connectionID) IN
                    \/ connection'.state = connection.state
                    \/ connection.state = "UNINIT" => (connection'.state = "INIT" \/ connection'.state = "TRYOPEN")]_vars

SafeHandShake2 == [] [\A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connection == getConnectionEnd(chainID, connectionID) IN
                    \/ connection'.state = connection.state
                    \/ (connection.state = "INIT" \/ connection.state = "TRYOPEN" \/ connection.state = "OPEN") => connection'.state = "OPEN"]_vars


SafeHandShake == 
                 /\ SafeHandShake1
                 /\ SafeHandShake2

LiveConnOpen1 == \A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connectionEnd == getConnectionEnd(chainID, connectionID) IN
                       [] (<> (connectionEnd.state = "OPEN"))


LiveConnOpen2 == \A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connectionEnd == getConnectionEnd(chainID, connectionID)
                        counterpartyConnectionEnd == 
                                getConnectionEnd(getCounterpartyChainID(chainID), connectionEnd.counterpartyConnectionID) IN
                    []((connectionEnd.state = "TRYOPEN" /\ counterpartyConnectionEnd.state = "INIT") => <>(connectionEnd.state = "OPEN"))

LiveConnOpen3 == \A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connectionEnd == getConnectionEnd(chainID, connectionID)
                        counterpartyConnectionEnd == 
                                getConnectionEnd(getCounterpartyChainID(chainID), connectionEnd.counterpartyConnectionID) IN
                                        []((connectionEnd.state = "TRYOPEN" /\ counterpartyConnectionEnd.state = "INIT" /\ <>(counterpartyConnectionEnd.counterpartyConnectionID = connectionID)) => <>(connectionEnd.state = "OPEN"))

LiveHandShake == /\ LiveConnOpen1
                 \*/\ LiveConnOpen2
                 \*/\ LiveConnOpen3


CorrectOpen== \A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connectionEnd == getConnectionEnd(chainID, connectionID) IN
                    [] ( connectionEnd.state = "OPEN" =>
                        LET counterpartyConnectionEnd == 
                                getConnectionEnd(getCounterpartyChainID(chainID), connectionEnd.counterpartyConnectionID) IN
                        <> (counterpartyConnectionEnd.state = "OPEN") 
                        )  


CorrectVersion == \A chainID \in ChainIDs, connectionID \in ConnectionIDs: 
                    LET connectionEnd == getConnectionEnd(chainID, connectionID) IN
                    [] (connectionEnd.state = "OPEN" =>
                        LET counterpartyConnectionEnd == 
                                getConnectionEnd(getCounterpartyChainID(chainID), connectionEnd.counterpartyConnectionID) IN
                        <> (counterpartyConnectionEnd.versions = connectionEnd.versions) 
                        ) 


CorrectHandShake == /\ CorrectOpen
                    /\ CorrectVersion 


Redundancy1 == [][\A connectionID \in ConnectionIDs, counterpartyConnectionID \in ConnectionIDs, version \in SUBSET Versions:
                    LET 
                        ChainAconnectionEnd == getConnectionEnd("chainA", connectionID) 
                        proofA == proofConnectionState("chainA", connectionID)
                        ChainBconnectionEnd == getConnectionEnd("chainB", connectionID) 
                        proofB == proofConnectionState("chainB", connectionID)
                    IN 
                    /\ ChainA!HandleConnOpenAck(connectionID, counterpartyConnectionID, version, proofB) => ChainAconnectionEnd.state /= "TRYOPEN"
                    /\ ChainB!HandleConnOpenAck(connectionID, counterpartyConnectionID, version, proofA) => ChainBconnectionEnd.state /= "TRYOPEN"
                ]_vars
                

Redundancy2 == \A chainID \in ChainIDs, connectionID \in ConnectionIDs:
                    LET 
                        connectionEnd == getConnectionEnd(chainID, connectionID)
                        counterpartyConnectionEnd == getConnectionEnd(getCounterpartyChainID(chainID), connectionEnd.counterpartyConnectionID)
                    IN 
                [] (connectionEnd.state = "INIT" => counterpartyConnectionEnd.state = "UNINIT")


CorrectImpl == 
        /\ Redundancy1
        /\ Redundancy2

Pro == 
    /\ SafeHandShake
    /\ LiveHandShake
    /\ CorrectHandShake

=============================================================================