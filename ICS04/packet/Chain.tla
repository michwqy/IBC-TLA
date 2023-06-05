------------------------ MODULE Chain -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxChannelID, MaxPortID, MaxSeq, MaxVersion, MaxConnectionID, chainID, counterpartyChainID

VARIABLES chainStore, packetLog, packetIsTimeout

vars == <<chainStore, packetLog, packetIsTimeout>>

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

\*packet
nullSeq == 0
Seqs == 1..MaxSeq

Receipt(portID, channelID, sequence, state) == 
    [
        portID |-> portID,
        channelID |-> channelID,
        sequence |-> sequence,
        state |->  state
    ]

nullReceipt ==
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq,
        state |-> "none"        
    ]

Commit(portID, channelID, sequence) ==
    [
        portID |-> portID,
        channelID |-> channelID,
        sequence |-> sequence        
    ]

nullCommit == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq      
    ]    

Ack(portID, channelID, sequence) ==
    [
        portID |-> portID,
        channelID |-> channelID,
        sequence |-> sequence        
    ]

nullAck == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq      
    ]    

\*chain
ChainStore(client, connections, channelEnds, nextSequenceSend, 
            nextSequenceRecv, nextSequenceAck, commitments, receipts, acks, nextChannelID) == 
    [
        chainID |-> chainID,
        client |-> client,
        connections |-> connections,
        channelEnds |-> channelEnds,
        nextSequenceSend |-> nextSequenceSend,
        nextSequenceRecv |-> nextSequenceRecv,
        nextSequenceAck |-> nextSequenceAck,
        commitments |-> commitments, 
        receipts |-> receipts,
        acks |-> acks,
        nextChannelID |-> nextChannelID
    ]

\* packet log
LogEntry(portID, channelID, seq, type) ==
    [
        portID |-> portID,
        channelID |-> channelID,
        seq |-> seq,
        type |-> type
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

getNextSeqSend(portID, channelID) == 
    LET seqSend == getChainStore.nextSequenceSend IN 
    IF channelID \in DOMAIN seqSend
    THEN seqSend[channelID]
    ELSE nullSeq

getNextSeqRecv(portID, channelID) == 
    LET seqRecv == getChainStore.nextSequenceRecv IN 
    IF channelID \in DOMAIN seqRecv 
    THEN seqRecv[channelID]
    ELSE nullSeq

getNextSeqAck(portID, channelID) == 
    LET seqAck == getChainStore.nextSequenceAck IN 
    IF channelID \in DOMAIN seqAck
    THEN seqAck[channelID]
    ELSE nullSeq

getPacketReceipt(portID, channelID, sequence) ==
    LET receipts == getChainStore.receipts IN
    IF channelID \in DOMAIN receipts /\ sequence \in {x.sequence : x \in receipts[channelID]}
    THEN CHOOSE x \in receipts[channelID]: x.sequence = sequence
    ELSE nullReceipt

getPacketAck(portID, channelID, sequence) ==
    LET acks == getChainStore.acks IN
    IF channelID \in DOMAIN acks /\ sequence \in {x.sequence : x \in acks[channelID]}
    THEN CHOOSE x \in acks[channelID]: x.sequence = sequence
    ELSE nullAck

getPacketCommit(portID, channelID, sequence) ==
    LET commits == getChainStore.commitments IN
    IF channelID \in DOMAIN commits /\ sequence \in {x.sequence : x \in commits[channelID]}
    THEN CHOOSE x \in commits[channelID]: x.sequence = sequence
    ELSE nullCommit

verifyChannelState(proof, portID, channelID, expected) ==
    LET counterpartychainID == getCounterpartyChainID IN 
    /\ counterpartychainID = proof.chainID 
    /\ expected = proof.channel

verifyPacketData(proof, portID, channelID, sequence) ==
    LET 
        counterpartychainID == getCounterpartyChainID 
        commit == Commit(portID, channelID, sequence)
    IN 
    /\ counterpartychainID = proof.chainID 
    /\ commit = proof.commit 

verifyPacketAck(proof, portID, channelID, sequence) ==
    LET 
        counterpartychainID == getCounterpartyChainID 
        ack == Ack(portID, channelID, sequence)
    IN 
    /\ counterpartychainID = proof.chainID 
    /\ ack = proof.ack   

verifyNextSeqRecv(proof, portID, channelID, nextSeqRecv) == 
    LET 
        counterpartychainID == getCounterpartyChainID 
    IN 
    /\ counterpartychainID = proof.chainID 
    /\ proof.nextSeqRecv = nextSeqRecv  

verifyPacketReceiptAbsence(proof, portID, channelID, sequence) == 
    LET 
        counterpartychainID == getCounterpartyChainID 
    IN 
    /\ counterpartychainID = proof.chainID       
    /\ proof.receipt = nullReceipt

verifyPacketReceipt(proof, portID, channelID, sequence, state) == 
    LET 
        counterpartychainID == getCounterpartyChainID 
    IN 
    /\ counterpartychainID = proof.chainID 
    /\ proof.receipt.portID = portID 
    /\ proof.receipt.channelID = channelID 
    /\ proof.receipt.sequence = sequence     
    /\ proof.receipt.state = state

isSendTimeout(sequence) == 
    packetIsTimeout[chainID][sequence]

isRecvTimeout(sequence) == 
    packetIsTimeout[counterpartyChainID][sequence]

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
                                                        !.nextSequenceSend = Append(chainStore.nextSequenceSend, 1),
                                                        !.nextSequenceRecv = Append(chainStore.nextSequenceRecv, 1),
                                                        !.nextSequenceAck = Append(chainStore.nextSequenceAck, 1),
                                                        !.commitments = @ \o << {} >>, 
                                                        !.receipts = @ \o << {} >>,
                                                        !.acks = @ \o << {} >>,
                                                        !.nextChannelID = @+1
                                                        ]
        /\ UNCHANGED <<packetLog, packetIsTimeout>>

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
                                                        !.nextSequenceSend = Append(chainStore.nextSequenceSend, 1),
                                                        !.nextSequenceRecv = Append(chainStore.nextSequenceRecv, 1),
                                                        !.nextSequenceAck = Append(chainStore.nextSequenceAck, 1),
                                                        !.commitments = @ \o << {} >>, 
                                                        !.receipts = @ \o << {} >>,
                                                        !.acks = @ \o << {} >>,
                                                        !.nextChannelID = @+1
                                                        ]
        /\ UNCHANGED <<packetLog, packetIsTimeout>>

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
        /\ UNCHANGED <<packetLog, packetIsTimeout>>

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
        /\ UNCHANGED <<packetLog, packetIsTimeout>>

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
        /\ UNCHANGED <<packetLog, packetIsTimeout>>

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
        /\ UNCHANGED <<packetLog, packetIsTimeout>>
    
\* packet lifecycle
HandleSendPacket(sourcePort, sourceChannel) == 
    LET 
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        seq == getNextSeqSend(sourcePort, sourceChannel)
        log == LogEntry(sourcePort, sourceChannel, seq, "send")
        commit == Commit(sourcePort, sourceChannel, seq)
    IN 
    /\ seq <= MaxSeq \*使得行为有限
    /\ channel /= nullChannelEnd
    /\ channel.state /= "CLOSED"
    /\ connection /= nullConnectionEnd
    /\ chainStore' = [chainStore EXCEPT 
                                !.nextSequenceSend = [chainStore.nextSequenceSend EXCEPT ![sourceChannel] = seq+1],
                                !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \union {commit}]]
    /\ packetLog' = Append(packetLog, log)

HandleRecvPacketandWriteAcknowledgement(sourcePort, sourceChannel, destPort, destChannel, sequence, proof) == 
    LET 
        channel == getChannelEnd(destPort, destChannel)
        connection == getConnection(channel.connectionID)
        nextSeqRecv == getNextSeqRecv(sourcePort, sourceChannel)
        log == LogEntry(destPort, destChannel, sequence, "recv")
        successReceipt == Receipt(destPort, destChannel, sequence, "SUCCESS")
        timeoutReceipt == Receipt(destPort, destChannel, sequence, "TIMEOUT") 
        receipt == getPacketReceipt(destPort, destChannel, sequence)
        ack == Ack(destPort, destChannel, sequence)
    IN 
    /\ channel /= nullChannelEnd
    /\ channel.state = "OPEN"
    /\ sourcePort = channel.counterpartyPortID
    /\ sourceChannel = channel.counterpartyChannelID
    /\ connection /= nullConnectionEnd
    /\ connection.state = "OPEN"
    /\ verifyPacketData(proof, sourcePort, sourceChannel, sequence)
    /\
        \/ 
            /\ channel.order = "ORDERED"
            /\ sequence = nextSeqRecv
            /\ ~isRecvTimeout(sequence)
            /\ chainStore' = [chainStore EXCEPT 
                                !.nextSequenceRecv = [chainStore.nextSequenceRecv EXCEPT ![destChannel] = nextSeqRecv+1],
                                !.acks = [chainStore.acks EXCEPT ![destChannel] = @ \union {ack}]]
        \/
            /\ channel.order = "ORDERED_ALLOW_TIMEOUT"
            /\ sequence = nextSeqRecv
            /\ IF isRecvTimeout(sequence)
                THEN chainStore' = [chainStore EXCEPT 
                                    !.nextSequenceRecv = [chainStore.nextSequenceRecv EXCEPT ![destChannel] = nextSeqRecv+1],
                                    !.receipts = [chainStore.receipts EXCEPT ![destChannel] = @ \union {timeoutReceipt}]]
                ELSE chainStore' = [chainStore EXCEPT 
                                    !.nextSequenceRecv = [chainStore.nextSequenceRecv EXCEPT ![destChannel] = nextSeqRecv+1],
                                    !.acks = [chainStore.acks EXCEPT ![destChannel] = @ \union {ack}]]
        \/ 
            /\ channel.order = "UNORDERED"
            /\ ~isRecvTimeout(sequence)
            /\ receipt = nullReceipt
            /\ chainStore' = [chainStore EXCEPT 
                                    !.receipts = [chainStore.receipts EXCEPT ![destChannel] = @ \union {successReceipt}],
                                    !.acks = [chainStore.acks EXCEPT ![destChannel] = @ \union {ack}]]
    /\ packetLog' = Append(packetLog, log)

HandleAcknowledgePacket(sourcePort, sourceChannel, destPort, destChannel, sequence, proof) == 
    LET 
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        nextSeqAck == getNextSeqAck(sourcePort, sourceChannel)
        log == LogEntry(sourcePort, sourceChannel, sequence, "ack")
        commit == getPacketCommit(sourcePort, sourceChannel, sequence)
    IN     
    /\ channel /= nullChannelEnd
    /\ channel.state = "OPEN"
    /\ destPort = channel.counterpartyPortID
    /\ destChannel = channel.counterpartyChannelID
    /\ connection /= nullConnectionEnd
    /\ connection.state = "OPEN"
    /\ commit = Commit(sourcePort, sourceChannel, sequence)
    /\ verifyPacketAck(proof, destPort, destChannel, sequence)
    /\ 
        \/
            /\ channel.order = "ORDERED" \/ channel.order = "ORDERED_ALLOW_TIMEOUT"
            /\ nextSeqAck = sequence
            /\ chainStore' = [chainStore EXCEPT 
                                    !.nextSequenceAck = [chainStore.nextSequenceAck EXCEPT ![sourceChannel] = nextSeqAck+1],
                                    !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]
        \/ 
            /\ channel.order = "UNORDERED"
            /\ chainStore' = [chainStore EXCEPT
                                    !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]
    /\ packetLog' = Append(packetLog, log)

HandleTimeoutPacket(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proof) ==
    LET 
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        commit == getPacketCommit(sourcePort, sourceChannel, sequence)
        log == LogEntry(sourcePort, sourceChannel, sequence, "timeout")
        nextSeqAck == getNextSeqAck(sourcePort, sourceChannel)        
    IN 
    /\ channel /= nullChannelEnd
    /\ destChannel = channel.counterpartyChannelID
    /\ destPort = channel.counterpartyPortID 
    /\ isSendTimeout(sequence)
    /\ commit = Commit(sourcePort, sourceChannel, sequence)
    /\ 
        \/ 
            /\ channel.order = "ORDERED"
            /\ nextSeqRecv = sequence
            /\ verifyNextSeqRecv(proof, destPort, destChannel, nextSeqRecv)
            /\ chainStore' = [chainStore EXCEPT
                                    !.channelEnds = [chainStore.channelEnds EXCEPT ![sourceChannel] = [chainStore.channelEnds[sourceChannel] EXCEPT !.state = "CLOSED"]],
                                    !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]
        \/
            /\ channel.order = "UNORDERED"
            /\ verifyPacketReceiptAbsence(proof, destPort, destChannel, sequence)
            /\ chainStore' = [chainStore EXCEPT
                                    !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]
        \/
            /\ channel.order = "ORDERED_ALLOW_TIMEOUT"
            /\ nextSeqAck = sequence
            /\ 
                \*\/ nextSeqRecv = sequence
                \*\/ verifyPacketReceipt(proof, destPort, destChannel, sequence, "TIMEOUT_RECEIPT")
                /\ nextSeqRecv = sequence
                /\ verifyPacketReceipt(proof, destPort, destChannel, sequence, "TIMEOUT_RECEIPT")
            /\ chainStore' = [chainStore EXCEPT
                                    !.nextSequenceAck = [chainStore.nextSequenceAck EXCEPT ![sourceChannel] = @+1],
                                    !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]    
    /\ packetLog' = Append(packetLog, log)

HandleTimeoutOnClose(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proofChannel, proof) == 
    LET 
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        commit == getPacketCommit(sourcePort, sourceChannel, sequence)
        expected == ChannelEnd(channel.counterpartyPortID, channel.counterpartyChannelID, "CLOSED", channel.order, channel.portID, channel.channelID, connection.counterpartyConnectionID, channel.version)
        log == LogEntry(sourcePort, sourceChannel, sequence, "close")
    IN
    /\
        \/
            /\ destChannel = channel.counterpartyChannelID
            /\ destPort = channel.counterpartyPortID
            /\ commit = Commit(sourcePort, sourceChannel, sequence)
            /\ verifyChannelState(proofChannel, channel.counterpartyPortID, channel.counterpartyChannelID, expected)
        \*\/
            \*/\ channel.state = "CLOSED"
            \*/\ commit /= nullCommit 
    /\ 
        \/
            /\ channel.order = "ORDERED" \/ channel.order = "ORDERED_ALLOW_TIMEOUT"
            /\ verifyNextSeqRecv(proof, destPort, destChannel, nextSeqRecv)
            /\ 
                \/ nextSeqRecv <= sequence
                \*\/ verifyPacketReceipt(proof, destPort, destChannel, sequence, "TIMEOUT_RECEIPT")
        \/ 
            /\ channel.order = "UNORDERED"
            /\ verifyPacketReceiptAbsence(proof, destPort, destChannel, sequence)
    /\ chainStore' = [chainStore EXCEPT
                                !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]
    /\ packetLog' = Append(packetLog, log)

\*init functions
InitClient ==
    Client(1)

InitConnetions == 
    <<ConnectionEnd("OPEN", 1, 1, 1, 1, {1})>>

InitChainStore ==
    ChainStore(InitClient, InitConnetions, <<>>, <<>>, <<>>, <<>>, <<>>, <<>>, <<>>, 1)

Init == 
    /\ chainStore = InitChainStore
    /\ packetLog = <<>>

HandleChannel(order, connectionID, portID, channelID, counterpartyPortID, counterpartyChannelID, version, counterpartyVersion, proof) == 
    /\
        \/ HandlechanOpenInit(order, connectionID, portID, counterpartyPortID, version)
        \/ HandlechanOpenTry(order, connectionID, portID, counterpartyPortID, counterpartyChannelID, version, counterpartyVersion, proof)  
        \/ HandlechanOpenAck(portID, channelID, counterpartyChannelID, counterpartyVersion, proof)
        \/ HandlechanOpenConfirm(portID, channelID, proof)
        \/ HandlechanCloseInit(portID, channelID)
        \/ HandlechanCloseConfirm(portID, channelID, proof)
    /\ UNCHANGED packetIsTimeout

HandlePacket(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proofChannelState, proofSource, proofDest) == 
    /\
        \/ HandleSendPacket(sourcePort, sourceChannel)
        \/ HandleRecvPacketandWriteAcknowledgement(sourcePort, sourceChannel, destPort, destChannel, sequence, proofSource) 
        \/ HandleAcknowledgePacket(sourcePort, sourceChannel, destPort, destChannel, sequence, proofDest)
        \/ HandleTimeoutPacket(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proofDest)
        \/ HandleTimeoutOnClose(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proofChannelState, proofDest)
    /\ UNCHANGED packetIsTimeout

TypeOK == 
        /\ \A channelID \in DOMAIN chainStore.channelEnds : chainStore.channelEnds[channelID] \in ChannelEnds(Versions)

=============================================================================