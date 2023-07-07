------------------------ MODULE Chain -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxConnectionID, MaxVersion, chainID, counterpartyChainID, ClientID

VARIABLES chainStore

vars == <<chainStore>>

ClientIDs == {ClientID}
nullClientID == "none"

nullConnectionID == 0

ConnectionEnd(state, connectionID, counterpartyConnectionID, clientID, counterpartyClientID, version) == 
    [
        state |-> state,
        connectionID |-> connectionID,
        clientID |-> clientID,
        counterpartyConnectionID |-> counterpartyConnectionID,
        counterpartyClientID |-> counterpartyClientID,
        versions |-> version
    ]

nullClient == 
    [
        clientID |-> nullClientID
    ]

nullConnectionEnd == 
    [
        state |-> "UNINIT",
        connectionID |-> nullConnectionID,
        clientID |-> nullClientID,
        counterpartyConnectionID |-> nullConnectionID,
        counterpartyClientID |-> nullClientID,
        versions |-> {}
    ]

getChainStore ==
    chainStore

queryClient(clientID) == 
    LET chainstore == getChainStore 
        client == chainstore.client IN 
    IF clientID = client.clientID 
    THEN client 
    ELSE nullClient

queryConnection(connectionID) == 
    LET chainstore == getChainStore
        connections == chainstore.connectionEnds IN 
    IF connectionID \in DOMAIN connections
    THEN connections[connectionID]
    ELSE nullConnectionEnd

getCompatibleVersions ==
    chainStore.compatibleVersions

generateID == 
    LET chainstore == getChainStore
        nextID == chainstore.nextConnectionID IN 
    IF nextID <= MaxConnectionID 
    THEN nextID
    ELSE nullConnectionID

pickVersion(versions) == 
    IF versions /= {}
    THEN LET version == CHOOSE x \in versions: TRUE IN 
        {version}
    ELSE {}
            
verifyConnectionState(proof, connectionID, expected) ==
    /\ counterpartyChainID = proof.chainID 
    /\ expected = proof.connection

HandleConnOpenInit(clientID, counterpartyClientID, version) ==
    LET 
        ID == generateID
        client == queryClient(clientID)
        connection == queryConnection(ID)
        state == "INIT"
        compatibleVersions == getCompatibleVersions
        versions == 
            IF compatibleVersions \intersect version /= {}
            THEN compatibleVersions \intersect version
            ELSE compatibleVersions 
    IN
    /\ ID /= nullConnectionID 
    /\ client /= nullClient 
    /\ connection = nullConnectionEnd 
    /\ chainStore' = [chainStore EXCEPT !.connectionEnds = Append(chainStore.connectionEnds,
                                                                    ConnectionEnd(state, ID, nullConnectionID, 
                                                                                clientID, counterpartyClientID, version)),
                                        !.nextConnectionID= @+1]


HandleConnOpenTry(clientID, counterpartyClientID, counterpartyConnectionID, counterpartyVersions, proofInit) ==
    LET 
        ID == generateID
        client == queryClient(clientID)
        state == "TRYOPEN"
        compatibleVersions == getCompatibleVersions
        versions == pickVersion(compatibleVersions \intersect counterpartyVersions)
        expectConnectionEnd == ConnectionEnd("INIT", counterpartyConnectionID, nullConnectionID, counterpartyClientID, clientID, counterpartyVersions) 
    IN
    /\ ID /= nullConnectionID 
    /\ client /= nullClient 
    /\ versions /= {} 
    /\ verifyConnectionState(proofInit, counterpartyConnectionID, expectConnectionEnd)
    /\ chainStore' = [chainStore EXCEPT !.connectionEnds = Append(chainStore.connectionEnds,
                                                                    ConnectionEnd(state, ID, counterpartyConnectionID, 
                                                                                clientID, counterpartyClientID, counterpartyVersions)),
                                        !.nextConnectionID= @+1]

HandleConnOpenAck(connectionID, counterpartyConnectionID, version, proofTry) == 
    LET 
        connection == queryConnection(connectionID) 
        state == "OPEN"
        expectConnectionEnd == ConnectionEnd("TRYOPEN", counterpartyConnectionID, connectionID, connection.counterpartyClientID, 
                                                connection.clientID, version) 
    IN
    /\ connection /= nullConnectionEnd
    /\ connection.state = "INIT" 
    /\ version \intersect connection.versions /= {} 
    /\ verifyConnectionState(proofTry, counterpartyConnectionID, expectConnectionEnd)
    /\ chainStore'  = [chainStore EXCEPT !.connectionEnds = [chainStore.connectionEnds EXCEPT 
                                    ![connectionID] = [chainStore.connectionEnds[connectionID] EXCEPT 
                                            !.state = state, 
                                            !.versions = version,
                                            !.counterpartyConnectionID = counterpartyConnectionID]]]

HandleConnOpenConfirm(connectionID, proofAck) == 
    LET 
        connection == queryConnection(connectionID)
        state == "OPEN"
        expectConnectionEnd == ConnectionEnd("OPEN", connection.counterpartyConnectionID, connectionID, connection.counterpartyClientID, 
                                            connection.clientID, connection.versions)
    IN
    /\ connection /= nullConnectionEnd
    /\ connection.state = "TRYOPEN" 
    /\ verifyConnectionState(proofAck, connection.counterpartyConnectionID, expectConnectionEnd)
    /\ chainStore'  = [chainStore EXCEPT !.connectionEnds = [chainStore.connectionEnds EXCEPT 
                                    ![connectionID] = [chainStore.connectionEnds[connectionID] EXCEPT 
                                            !.state = state]]]

InitClient == 
    [
        clientID |-> ClientID
    ]

InitChainStore(versions) == 
    [
        client : {InitClient},
        connectionEnds : {<<>>},
        nextConnectionID : {1},
        compatibleVersions : (SUBSET versions) \ {{}}
    ]

HandleChannel(clientID, counterpartyClientID, connectionID, counterpartyConnectionID, version, proof) == 
    \/ HandleConnOpenInit(clientID, counterpartyClientID, version)
    \/ HandleConnOpenTry(clientID, counterpartyClientID, counterpartyConnectionID, version, proof)
    \/ HandleConnOpenAck(connectionID, counterpartyConnectionID, version, proof)
    \/ HandleConnOpenConfirm(connectionID, proof)
    
Init(versions) == 
    /\ chainStore \in InitChainStore(versions)

=================