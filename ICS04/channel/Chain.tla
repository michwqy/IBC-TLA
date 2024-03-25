------------------------ MODULE Chain -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxChannelID, MaxPortID, MaxVersion, MaxConnectionID, chainID, counterpartyChainID

VARIABLES chainStore, allowCloseChannel

vars == <<chainStore>>

\*client
nullHeight == 0
nullClientID == 0
Client(clientID) == 
    [
        clientID |-> clientID
    ]
\*connection
nullConnectionID == 0
ConnectionIDs == 1..MaxConnectionID

ConnectionEnd(state, connectionID, counterpartyConnectionID, clientID, 
    counterpartyClientID, version) == 
    [
        state |-> state,
        connectionID |-> connectionID,
        clientID |-> clientID,
        counterpartyConnectionID |-> counterpartyConnectionID,
        counterpartyClientID |-> counterpartyClientID,
        versions |-> version
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

\*port
nullPortID == 0
PortIDs == 1..MaxPortID

\* channel
Versions == 1..MaxVersion
nullOrder == "none"
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
        order |-> nullOrder,
        counterpartyPortID |-> nullPortID,
        counterpartyChannelID |-> nullChannelID,
        connectionID |-> nullConnectionID,
        version |-> nullVersion
    ]

ChannelEnds(versions) == 
    [
        portID: PortIDs \union {nullPortID},
        channelID: ChannelIDs \union {nullChannelID},
        state: ChannelStates,
        order: Orders,
        counterpartyPortID: PortIDs \union {nullPortID},
        counterpartyChannelID: ChannelIDs \union {nullChannelID},
        connectionID: ConnectionIDs \union {nullConnectionID},
        version: versions
    ]

ChannelEnd(portID, channelID, state, order, counterpartyPortID, counterpartyChannelID, connectionID, version) == 
    [
        portID |-> portID,
        channelID |-> channelID,
        state |-> state,
        order |-> order,
        counterpartyPortID |-> counterpartyPortID,
        counterpartyChannelID |-> counterpartyChannelID,
        connectionID |-> connectionID,
        version |-> version 
    ]

\*chain
ChainStore(client, connections, channelEnds, nextChannelID) == 
    [
        client |-> client,
        connections |-> connections,
        channelEnds |-> channelEnds,
        nextChannelID |-> nextChannelID
    ]

\* help functions
getChainStore ==
    chainStore

getChannelEnd(portID, channelID) ==
    LET chainstore == getChainStore
        channelEnds == chainstore.channelEnds IN 
    IF channelID \in DOMAIN channelEnds /\ channelEnds[channelID].portID = portID
    THEN channelEnds[channelID]
    ELSE nullChannelEnd

getConnection(connectionID) == 
    LET chainstore == getChainStore
        connections == chainstore.connections IN 
    IF connectionID \in DOMAIN connections
    THEN connections[connectionID]
    ELSE nullConnectionEnd

generateID == 
    LET chainstore == getChainStore
        nextID == chainstore.nextChannelID IN 
    IF nextID <= MaxChannelID 
    THEN nextID
    ELSE nullChannelID

getCounterpartyChainID == 
    counterpartyChainID

verifyChannelState(proof, portID, channelID, expected) ==
    LET counterpartychainID == getCounterpartyChainID IN 
    /\ counterpartychainID = proof.chainID 
    /\ expected = proof.channel

\* channel lifecycle
HandlechanOpenInit(order, connectionID, portID, counterpartyPortID, version) == 
    LET 
        channelID == generateID
        channelEnd == getChannelEnd(portID, channelID)
        connection == getConnection(connectionID)
        channel == ChannelEnd(portID, channelID, "INIT", order, counterpartyPortID, nullChannelID, connectionID, version)
    IN 
        /\ channelID /= nullChannelID
        /\ channelEnd = nullChannelEnd
        /\ connection /= nullConnectionEnd
        /\ chainStore' = [chainStore EXCEPT !.channelEnds = Append(chainStore.channelEnds, channel),
                                                        !.nextChannelID = @+1
                                                        ]

HandlechanOpenTry(order, connectionID, portID, counterpartyPortID, 
        counterpartyChannelID, version, counterpartyVersion, proofInit) == 
    LET 
        channelID == generateID
        connection == getConnection(connectionID)  
        expected == ChannelEnd(counterpartyPortID, counterpartyChannelID, "INIT", order, portID, nullChannelID, connection.counterpartyConnectionID, counterpartyVersion)
        channel == ChannelEnd(portID, channelID, "TRYOPEN", order, counterpartyPortID, counterpartyChannelID, connectionID, version)
    IN 
        /\ channelID /= nullChannelID
        /\ connection /= nullConnectionEnd
        /\ connection.state = "OPEN" 
        /\ verifyChannelState(proofInit, counterpartyPortID, counterpartyChannelID, expected)
        /\ chainStore' = [chainStore EXCEPT !.channelEnds = Append(chainStore.channelEnds, channel),
                                                            !.nextChannelID = @+1
                                                        ]

HandlechanOpenAck(portID, channelID, counterpartyChannelID, counterpartyVersion, proofTry) ==
    LET 
        channel == getChannelEnd(portID, channelID)
        connectionID == channel.connectionID
        connection == getConnection(connectionID)  
        expected == ChannelEnd(channel.counterpartyPortID, counterpartyChannelID, "TRYOPEN", channel.order, portID, channelID, connection.counterpartyConnectionID, counterpartyVersion)
        newChannel == [channel EXCEPT !.state = "OPEN", !.version = counterpartyVersion, !.counterpartyChannelID = counterpartyChannelID]
    IN 
        /\ channel.state = "INIT"
        /\ connection /= nullConnectionEnd
        /\ connection.state = "OPEN" 
        /\ verifyChannelState( proofTry, channel.counterpartyPortID, counterpartyChannelID, expected)
        /\ chainStore' = [chainStore EXCEPT !.channelEnds = [chainStore.channelEnds EXCEPT ![channelID] = newChannel]]

HandlechanOpenConfirm(portID, channelID, proofAck) ==
    LET 
        channel == getChannelEnd(portID, channelID)
        connectionID == channel.connectionID
        connection == getConnection(connectionID)  
        expected == ChannelEnd(channel.counterpartyPortID, channel.counterpartyChannelID, "OPEN", channel.order, portID, channelID, connection.counterpartyConnectionID, channel.version)
        newChannel == [channel EXCEPT !.state = "OPEN"]
    IN 
        /\ channel /= nullChannelEnd
        /\ channel.state = "TRYOPEN"
        /\ connection /= nullConnectionEnd
        /\ connection.state = "OPEN"
        /\ verifyChannelState(proofAck, channel.counterpartyPortID, channel.counterpartyChannelID, expected)
        /\ chainStore' = [chainStore EXCEPT !.channelEnds = [chainStore.channelEnds EXCEPT ![channelID] = newChannel]]

HandlechanCloseInit(portID, channelID) ==
    LET 
        channel == getChannelEnd(portID, channelID)
        connectionID == channel.connectionID
        connection == getConnection( connectionID)  
        newChannel == [channel EXCEPT !.state = "CLOSED"]
    IN 
        /\ channel /= nullChannelEnd
        /\ channel.state /= "CLOSED" 
        /\ connection /= nullConnectionEnd
        /\ connection.state = "OPEN"
        /\ chainStore' = [chainStore EXCEPT !.channelEnds = [chainStore.channelEnds EXCEPT ![channelID] = newChannel]]

HandlechanCloseConfirm(portID, channelID, proofInit) == 
    LET 
        channel == getChannelEnd(portID, channelID)
        connectionID == channel.connectionID
        connection == getConnection(connectionID)  
        newChannel == [channel EXCEPT !.state = "CLOSED"]
        expected == ChannelEnd(channel.counterpartyPortID, channel.counterpartyChannelID, "CLOSED", channel.order, portID, channelID, connection.counterpartyConnectionID, channel.version)
    IN 
        /\ channel /= nullChannelEnd
        /\ channel.state /= "CLOSED" 
        /\ connection /= nullConnectionEnd
        /\ connection.state = "OPEN"
        /\ verifyChannelState(proofInit, channel.counterpartyPortID, channel.counterpartyChannelID, expected)
        /\ chainStore' = [chainStore EXCEPT !.channelEnds = [chainStore.channelEnds EXCEPT ![channelID] = newChannel]]
    

\*init functions
InitClient ==
    Client(1)

InitConnetions == 
    <<ConnectionEnd("OPEN", 1, 1, 1, 1, {1})>>

InitChainStore ==
    ChainStore(InitClient, InitConnetions, <<>>, 1)

Init == 
    /\ chainStore = InitChainStore

HandleChannel(order, connectionID, portID, channelID, counterpartyPortID, counterpartyChannelID, version, counterpartyVersion, proof) == 
    /\
        \/ HandlechanOpenInit(order, connectionID, portID, counterpartyPortID, version)
        \/ HandlechanOpenTry(order, connectionID, portID, counterpartyPortID, counterpartyChannelID, version, counterpartyVersion, proof)  
        \/ HandlechanOpenAck(portID, channelID, counterpartyChannelID, counterpartyVersion, proof)
        \/ HandlechanOpenConfirm(portID, channelID, proof)
        \/  
            /\ allowCloseChannel
            /\ HandlechanCloseInit(portID, channelID)
        \/  
            /\ allowCloseChannel
            /\ HandlechanCloseConfirm(portID, channelID, proof)
    /\ UNCHANGED allowCloseChannel

TypeOK == 
        /\ \A channelID \in DOMAIN chainStore.channelEnds : chainStore.channelEnds[channelID] \in ChannelEnds(Versions)

=============================================================================