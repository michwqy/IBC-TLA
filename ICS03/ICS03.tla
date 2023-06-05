------------------------ MODULE ICS03 -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANT Maxheight, MaxVersion, MaxDelayPeriod, MaxConnectionID

VARIABLES chainA, chainB

vars == <<chainA, chainB>>

(*
Chain{
    chainID: Str
    height: Int
    client: Client
}
*)

(*
Client{
    clientID: Str
    counterpartyChainID: Str
    counterpartyHeights: Set(Int)
    connectionEnds: Seq(ConnectionEnd)
    versions: Set(Int)
    count: Int
}
*)

(*
ConnectionEnd{
    state: Str
    connectionID: Int
    counterpartyConnectionID: Int
    clientID: Str
    counterpartyClientID: Str
    channelEnds: Seq(ChannelEnd)
    version: Set(Int)
    delayPeriod: Int
}
*)

Heights == 1..Maxheight
Versions == 1..MaxVersion
DelayPeriods == 0..MaxDelayPeriod

\* chain
ChainIDs == {"chainA", "chainB"}
nullChainID == "none"

\* client
ClientIDs == {"clA", "clB"}
nullClientID == "none"
nullClient == 
    [
        clientID |-> nullClientID,
        counterpartyChainID |-> nullChainID,
        counterpartyHeights |-> <<>>,
        connectionEnds |-> <<>>,
        versions |-> {},
        count |-> 0
    ]

\* connection
ConnectionIDs == 1..MaxConnectionID

nullConnectionID == 0
nullConnectionEnd == 
    [
        state |-> "UNINIT",
        connectionID |-> nullConnectionID,
        clientID |-> nullClientID,
        counterpartyConnectionID |-> nullConnectionID,
        counterpartyClientID |-> nullClientID,
        versions |-> {},
        delayPeriod |-> 0
    ]

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

ConnectionEnds(versions, delayPeriods) == 
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyClientID : ClientIDs \union {nullClientID},
        versions : SUBSET versions, 
        delayPeriod : delayPeriods
    ]

ConnectionEnd(state, connectionID, counterpartyConnectionID, clientID, 
    counterpartyClientID, version, delayPeriod) == 
    [
        state |-> state,
        connectionID |-> connectionID,
        clientID |-> clientID,
        counterpartyConnectionID |-> counterpartyConnectionID,
        counterpartyClientID |-> counterpartyClientID,
        versions |-> version,
        delayPeriod |-> delayPeriod 
    ]

\* help function
queryChain(chainID) == 
    IF chainID = "chainA"
    THEN chainA
    ELSE chainB

queryCounterpartyChainID(chainID) == 
    IF chainID = "chainA"
    THEN "chainB"
    ELSE "chainA"

queryChainClients(chainID) == 
    IF chainID = "chainA"
    THEN {"clA"}
    ELSE {"clB"}

queryClient(chainID, clientID) == 
    LET chain == queryChain(chainID) IN
    IF chain.client.clientID = clientID
    THEN chain.client
    ELSE nullClient

queryConnection(chainID, clientID, connectionID) == 
    LET client == queryClient(chainID, clientID) IN
    IF connectionID \in DOMAIN client.connectionEnds
    THEN client.connectionEnds[connectionID]
    ELSE nullConnectionEnd

getCompatibleVersions(chainID, clientID) ==      
    LET client == queryClient(chainID, clientID) IN
    client.versions

generateID(chainID, clientID) ==
    LET client == queryClient(chainID, clientID) IN
    IF client.count+1 <= MaxConnectionID
    THEN client.count+1
    ELSE 0

queryChainLatestHeight(chainID) == 
    LET chain == queryChain(chainID) IN 
    chain.height 

queryClientLatestHeight(chainID, clientID) ==
    LET client == queryClient(chainID, clientID) IN
    IF Len(client.counterpartyHeights)>0
    THEN client.counterpartyHeights[Len(client.counterpartyHeights)]
    ELSE 0

verifyConnectionEnd(chainID, clientID, counterpartyClientID, expectConnectionEnd, proofHeight) == 
    LET 
        counterpartyChainID == queryCounterpartyChainID(chainID)
        counterpartyClient == queryClient(counterpartyChainID, counterpartyClientID)
        latestHeight == queryClientLatestHeight(chainID, clientID)
        delayPeriod == expectConnectionEnd.delayPeriod
        counterpartyConnectionEnds == counterpartyClient.connectionEnds 
    IN
    IF 
        /\ clientID /= counterpartyClientID 
        /\ expectConnectionEnd \in {counterpartyConnectionEnds[i]: i \in DOMAIN counterpartyConnectionEnds}
        /\ proofHeight + delayPeriod < latestHeight
    THEN TRUE
    ELSE FALSE

pickVersion(versions) == 
    IF versions /= {}
    THEN LET version == CHOOSE x \in versions: TRUE IN 
        {version}
    ELSE {}
            
\* connection handshake
HandleConnOpenInit(chainID, clientID, counterpartyClientID, version, delayPeriod) ==
    LET 
        ID == generateID(chainID, clientID)
        client == queryClient(chainID, clientID)
        state == "INIT"
        compatibleVersions == getCompatibleVersions(chainID, clientID)
        versions == 
            IF compatibleVersions \intersect version /= {}
            THEN compatibleVersions \intersect version
            ELSE compatibleVersions 
    IN
    /\ ID /= nullConnectionID /\  client /= nullClient /\ queryConnection(chainID, clientID, ID) = nullConnectionEnd 
    /\
        IF chainID = "chainA"
        THEN 
            /\ chainA' = [chainA EXCEPT !.client = [client EXCEPT !.connectionEnds = client.connectionEnds \o 
                                                            <<ConnectionEnd(state, ID, nullConnectionID, clientID, 
                                                                counterpartyClientID, versions, delayPeriod)>>,
                                        !.count = @+1]]
            /\ UNCHANGED <<chainB>>
        ELSE 
            /\ chainB' = [chainB EXCEPT !.client = [client EXCEPT !.connectionEnds = client.connectionEnds \o 
                                                            <<ConnectionEnd(state, ID, nullConnectionID, clientID, 
                                                                counterpartyClientID, versions, delayPeriod)>>,
                                        !.count = @+1]]
            /\ UNCHANGED <<chainA>>

HandleConnOpenTry(chainID, clientID, counterpartyClientID, counterpartyConnectionID, 
        counterpartyVersions, delayPeriod, proofHeight, consensusHeight) ==
    LET 
        counterpartyChainID == queryCounterpartyChainID(chainID)
        ID == generateID(chainID, clientID)
        client == queryClient(chainID, clientID)
        currentHeight == queryChainLatestHeight(chainID)
        state == "TRYOPEN"
        compatibleVersions == getCompatibleVersions(chainID, clientID)
        versions == pickVersion(compatibleVersions \intersect counterpartyVersions)
        expectConnectionEnd == ConnectionEnd("INIT", counterpartyConnectionID, nullConnectionID, counterpartyClientID, clientID, counterpartyVersions, delayPeriod) 
    IN
    /\ 
        /\ ID /= nullConnectionID 
        /\ client /= nullClient 
        /\ consensusHeight < currentHeight
        /\ versions /= {} 
        /\ verifyConnectionEnd(counterpartyChainID, clientID, counterpartyClientID, expectConnectionEnd, proofHeight)
    /\
        IF chainID = "chainA"
        THEN 
            /\ chainA' = [chainA EXCEPT !.client = [client EXCEPT !.connectionEnds = client.connectionEnds \o 
                                                            <<ConnectionEnd(state, ID, counterpartyConnectionID, clientID, 
                                                                counterpartyClientID, versions, delayPeriod)>>,
                                        !.count = @+1]]
            /\ UNCHANGED <<chainB>>
        ELSE 
            /\ chainB' = [chainB EXCEPT !.client = [client EXCEPT !.connectionEnds = client.connectionEnds \o 
                                                            <<ConnectionEnd(state, ID, counterpartyConnectionID, clientID, 
                                                                counterpartyClientID, versions, delayPeriod)>>,
                                        !.count = @+1]]
            /\ UNCHANGED <<chainA>>

HandleConnOpenAck(chainID, clientID, connectionID, counterpartyConnectionID, version, proofHeight, consensusHeight) == 
    LET 
        counterpartyChainID == queryCounterpartyChainID(chainID)
        client == queryClient(chainID, clientID)
        connection == queryConnection(chainID, clientID, connectionID) 
        currentHeight == queryChainLatestHeight(chainID)
        state == "OPEN"
        expectConnectionEnd == ConnectionEnd("TRYOPEN", counterpartyConnectionID, connectionID, connection.counterpartyClientID, 
                                                connection.clientID, version, connection.delayPeriod) 
    IN
    /\
        /\ consensusHeight < currentHeight
        /\ client /= nullClient 
        /\ connection.state = "INIT" /\ version \intersect connection.versions /= {} 
        /\ verifyConnectionEnd(counterpartyChainID, clientID, connection.counterpartyClientID, expectConnectionEnd, proofHeight)
    /\
        IF chainID = "chainA"
        THEN 
            /\ chainA' = [chainA EXCEPT !.client = [client EXCEPT 
                            !.connectionEnds = [client.connectionEnds EXCEPT 
                                    ![connectionID] = [client.connectionEnds[connectionID] EXCEPT 
                                            !.state = state, 
                                            !.versions = version]]]]
            /\ UNCHANGED <<chainB>>
        ELSE 
            /\ chainB' = [chainB EXCEPT !.client = [client EXCEPT 
                            !.connectionEnds = [client.connectionEnds EXCEPT 
                                    ![connectionID] = [client.connectionEnds[connectionID] EXCEPT 
                                            !.state = state, 
                                            !.versions = version]]]]
            /\ UNCHANGED <<chainA>>

HandleConnOpenConfirm(chainID, clientID, connectionID, proofHeight) == 
    LET 
        counterpartyChainID == queryCounterpartyChainID(chainID)
        client == queryClient(chainID, clientID)
        connection == queryConnection(chainID, clientID, connectionID)
        state == "OPEN"
        expectConnectionEnd == ConnectionEnd("OPEN", connection.counterpartyConnectionID, connectionID, connection.counterpartyClientID, 
                                            connection.clientID, connection.version, connection.delayPeriod)
    IN
    /\
        /\ client /= nullClient 
        /\ connection.state = "TRYOPEN" 
        /\ verifyConnectionEnd(counterpartyChainID, clientID, connection.counterpartyClientID, expectConnectionEnd, proofHeight)
    /\
        IF chainID = "chainA"
        THEN 
            /\ chainA' = [chainA EXCEPT !.client = [client EXCEPT 
                            !.connectionEnds = [client.connectionEnds EXCEPT 
                                    ![connectionID] = [client.connectionEnds[connectionID] EXCEPT 
                                            !.state = state]]]]
            /\ UNCHANGED <<chainB>>
        ELSE 
            /\ chainB' = [chainB EXCEPT !.client = [client EXCEPT 
                            !.connectionEnds = [client.connectionEnds EXCEPT 
                                    ![connectionID] = [client.connectionEnds[connectionID] EXCEPT 
                                            !.state = state]]]]
            /\ UNCHANGED <<chainA>>

\* init 
InitClient(chainID, clientID, versions) == 
    [
        clientID: clientID,
        counterpartyChainID: {queryCounterpartyChainID(chainID)},
        counterpartyHeights: {<<>>},
        connectionEnds: {<<>>},
        versions: (SUBSET versions) \ {{}},
        count: {0}
    ]
            
InitChain(chainID, versions) == 
    [
        chainID: {chainID},
        height: {1},
        client: InitClient(chainID, queryChainClients(chainID), versions)
    ]

Init == 
    /\ chainA \in InitChain("chainA", Versions)
    /\ chainB \in InitChain("chainB", Versions)

\* chain actions

AdvanceHeight(chainID) == 
    LET currentHeight == queryChainLatestHeight(chainID) IN
    /\ currentHeight < Maxheight
    /\
        IF chainID = "chainA"
        THEN 
            /\ chainA' = [chainA EXCEPT !.height = @+1]
            /\ UNCHANGED chainB
        ELSE 
            /\ chainB' = [chainB EXCEPT !.height = @+1]
            /\ UNCHANGED  chainA


ChainNext == 
    \E chainID \in ChainIDs: AdvanceHeight(chainID)

\* enviroment actions

UpdataClient(chainID, clientID, newHeight) ==
    LET 
        latestHeight == queryClientLatestHeight(chainID, clientID) 
    IN
    /\ clientID \in queryChainClients(chainID) /\ latestHeight < newHeight 
    /\
        IF chainID = "chainA"
        THEN 
            /\ chainA' = [chainA EXCEPT !.client = [chainA.client EXCEPT !.counterpartyHeights = @ \o <<newHeight>>]]
            /\ UNCHANGED chainB
        ELSE 
            /\ chainB' = [chainB EXCEPT !.client = [chainB.client EXCEPT !.counterpartyHeights = @ \o <<newHeight>>]]
            /\ UNCHANGED  chainA     


ConnectionHandShake(chainID, clientID, counterpartyClientID, connectionID, counterpartyConnectionID, 
                    version, delayPeriod, proofHeight, consensusHeight) == 
    \/ HandleConnOpenInit(chainID, clientID, counterpartyClientID, version, delayPeriod)
    \/ HandleConnOpenTry(chainID, clientID, counterpartyClientID, counterpartyConnectionID, version, delayPeriod, proofHeight, consensusHeight)
    \/ HandleConnOpenAck(chainID, clientID, connectionID, counterpartyConnectionID, version, proofHeight, consensusHeight) 
    \/ HandleConnOpenConfirm(chainID, clientID, connectionID, proofHeight)    


EnviromentNext == 
    \E chainID \in ChainIDs, clientID, counterpartyClientID \in ClientIDs, connectionID, 
        counterpartyConnectionID \in ConnectionIDs, version \in SUBSET Versions, delayPeriod \in DelayPeriods,
        newHeight, proofHeight, consensusHeight \in Heights:
    \/ ConnectionHandShake(chainID, clientID, counterpartyClientID, connectionID, counterpartyConnectionID, 
                    version, delayPeriod, proofHeight, consensusHeight)
    \/ UpdataClient(chainID, clientID, newHeight)

Next == 
    \/ ChainNext
    \/ EnviromentNext
    \/ UNCHANGED vars


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


TypeOK == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
            queryConnection(chainID, clientID, connectionID) \in ConnectionEnds(Versions, DelayPeriods)

\* 如果connectionEnd状态已经是INIT，不能再回到UNINIT

SafaConnOpenInit == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    [](connectionEnd /=  nullConnectionEnd 
                        /\ connectionEnd.state = "INIT" 
                        => ~(<> (connectionEnd.state =  "UNINIT")))

\* 如果connectionEnd状态已经是TRYOPEN，不能再回到UNINIT、INIT

SafaConnOpenTry == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    [](connectionEnd /=  nullConnectionEnd 
                        /\ connectionEnd.state = "TRYOPEN" 
                        => ~(<> (connectionEnd.state =  "UNINIT" 
                                \/ connectionEnd.state =  "INIT")))

\* 如果connectionEnd状态已经是OPEN，不能再回到UNINIT、INIT、TRYOPEN

SafaConnOpenConfirm == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    [](connectionEnd /=  nullConnectionEnd 
                        /\ connectionEnd.state = "OPEN" 
                        => ~(<> (connectionEnd.state =  "UNINIT" 
                                \/ connectionEnd.state =  "INIT"
                                \/ connectionEnd.state =  "TRYOPEN")))

SafeConnOpen == [] [\A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connection == queryConnection(chainID, clientID, connectionID) IN
                    \/ connection'.state = connection.state
                    \/ connection'.state = "OPEN" => (connection.state = "INIT" \/ connection.state = "TRYOPEN")]_vars

SafeHandShake == /\ SafaConnOpenInit
                 /\ SafaConnOpenTry
                 /\ SafaConnOpenConfirm
                 /\ SafeConnOpen

\* 所有connectionEnd状态最终会变成INIT或TRYOPEN或OPEN

LiveConnOpenState == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    [](connectionEnd /=  nullConnectionEnd => 
                        <> (connectionEnd.state = "INIT" \/ connectionEnd.state = "TRYOPEN" \/ connectionEnd.state = "OPEN"))

\* 所有connectionEnd状态最终会变成INIT或TRYOPEN

LiveConnOpenInit == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    <>(connectionEnd /=  nullConnectionEnd) => 
                        <> (connectionEnd.state = "INIT" \/ connectionEnd.state = "TRYOPEN")

\* 所有connectionEnd状态最终会变成OPEN

LiveConnOpenConfirm == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs: 
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    <>(connectionEnd /=  nullConnectionEnd) => 
                        <> (connectionEnd.state = "OPEN")

\* 至少有一个connectionEnd状态最终变成OPEN

LiveOneOpen == \E chainID \in ChainIDs: \E clientID \in ClientIDs: \E connectionID \in ConnectionIDs:
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN 
                    <>(connectionEnd /=  nullConnectionEnd) /\ <>(connectionEnd.state = "OPEN" ) 

LiveHandShake == /\ LiveConnOpenState
                 /\ LiveConnOpenInit


CorrectOpen== \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs:
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    [] ( connectionEnd.state = "OPEN" =>
                        LET counterpartyConnectionEnd == 
                                queryConnection(queryCounterpartyChainID(chainID), connectionEnd.counterpartyClientID, connectionEnd.counterpartyConnectionID) IN
                        <> (counterpartyConnectionEnd.state = "OPEN") 
                        )  

CorrectVersion == \A chainID \in ChainIDs: \A clientID \in ClientIDs: \A connectionID \in ConnectionIDs:
                    LET connectionEnd == queryConnection(chainID, clientID, connectionID) IN
                    [] (connectionEnd.state = "OPEN" =>
                        LET counterpartyConnectionEnd == 
                                queryConnection(queryCounterpartyChainID(chainID), connectionEnd.counterpartyClientID, connectionEnd.counterpartyConnectionID) IN
                        <> (counterpartyConnectionEnd.versions = connectionEnd.versions) 
                        ) 

CorrectHandShake == /\ CorrectOpen
                    /\ CorrectVersion 


=============================================================================
