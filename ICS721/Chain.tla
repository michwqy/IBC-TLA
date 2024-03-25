------- MODULE Chain --------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS chainID, nativeClassId, MaxSeq, counterpartyChainID, MaxID, EscrowAddress

VARIABLES chainStore, packetIsTimeout, accounts, packetLog


RECURSIVE All(_)
All(s) == 
    IF s = {} THEN TRUE ELSE
        LET x == CHOOSE x \in s: TRUE IN 
            All(s \ {x}) /\ x

RECURSIVE Any(_)
Any(s) == 
    IF s = {} THEN FALSE ELSE
        LET x == CHOOSE x \in s :TRUE IN 
            Any(s \ {x}) \/ x


Packet(sequence, sourcePort, sourceChannel, destPort, destChannel, data) == 
    [
        sequence |-> sequence,
        sourcePort |-> sourcePort,
        sourceChannel |-> sourceChannel,
        destPort |-> destPort,
        destChannel |-> destChannel,
        data |-> data
    ]

NonFungibleTokenPacketData(classId, tokenIds, sender, receiver) ==
    [
        classId |-> classId,
        tokenIds |-> tokenIds,
        sender |-> sender,
        receiver |-> receiver
    ]

nullData ==
    [
        classId |-> <<>>,
        tokenIds |-> {},
        sender |-> "",
        receiver |-> ""        
    ]

isPrefixMatch(classId, sourcePort, sourceChannel) ==
    IF Len(classId) < 2 \/ classId[1] /= sourceChannel
    THEN FALSE
    ELSE TRUE

getChannelEscrowAddresses(channelID) == 
    EscrowAddress

   
nullClientID == 0
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

nullPortID == "none"
nullOrder == "none"
nullVersion == "none"
nullChannelID == "none"
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

nullSeq == 0
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

Commit(portID, channelID, sequence, data) ==
    [
        portID |-> portID,
        channelID |-> channelID,
        sequence |-> sequence,
        data |-> data       
    ]

nullCommit == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq,     
        data |-> nullData
    ]    

Ack(portID, channelID, sequence, state) ==
    [
        portID |-> portID,
        channelID |-> channelID,
        sequence |-> sequence,
        state |-> state   
    ]

nullAck == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq,
        state |-> "none"   
    ]  

LogEntry(sender, sourceChannel, sequence, type) == 
    [
        sender |-> sender,
        sourceChannel |-> sourceChannel,
        sequence |-> sequence,
        type |-> type
    ]

nullAccount == "none"

getChainStore ==
    chainStore

getCounterpartyChainID == 
    counterpartyChainID

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

getNextSeqSend(portID, channelID) == 
    LET seqSend == getChainStore.nextSequenceSend IN 
    IF channelID \in DOMAIN seqSend
    THEN seqSend[channelID]
    ELSE nullSeq

getPacketReceipt(portID, channelID, sequence) ==
    LET receipts == getChainStore.receipts IN
    IF channelID \in DOMAIN receipts /\ sequence \in {x.sequence : x \in receipts[channelID]}
    THEN CHOOSE x \in receipts[channelID]: x.sequence = sequence
    ELSE nullReceipt

getPacketCommit(portID, channelID, sequence) ==
    LET commits == getChainStore.commitments IN
    IF channelID \in DOMAIN commits /\ sequence \in {x.sequence : x \in commits[channelID]}
    THEN CHOOSE x \in commits[channelID]: x.sequence = sequence
    ELSE nullCommit

verifyPacketData(proof, portID, channelID, sequence, data) ==
    LET
        counterpartychainID == getCounterpartyChainID  
        commit == Commit(portID, channelID, sequence, data)
    IN
    /\ counterpartychainID = proof.chainID  
    /\ commit = proof.commit   

verifyPacketAck(proof, portID, channelID, sequence, ack) ==
    LET
        counterpartychainID == getCounterpartyChainID  
    IN 
    /\ counterpartychainID = proof.chainID 
    /\ ack = proof.ack  

verifyPacketReceiptAbsence(proof, portID, channelID, sequence) ==
    LET counterpartychainID == getCounterpartyChainID IN 
    /\ counterpartychainID = proof.chainID       
    /\ proof.receipt = nullReceipt

isSendTimeout(sequence) == 
    packetIsTimeout[chainID][sequence]

isRecvTimeout(sequence) == 
    packetIsTimeout[counterpartyChainID][sequence]

sendPacket(sourcePort, sourceChannel, data) == 
    LET 
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        seq == getNextSeqSend(sourcePort, sourceChannel)
        commit == Commit(sourcePort, sourceChannel, seq, data)
    IN 
    /\ seq <= MaxSeq
    /\ channel /= nullChannelEnd
    /\ channel.state /= "CLOSED"
    /\ connection /= nullConnectionEnd
    /\ chainStore' = [chainStore EXCEPT 
                                !.nextSequenceSend = [chainStore.nextSequenceSend EXCEPT ![sourceChannel] = seq+1],
                                !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \union {commit}]] 

getOwner(classId, tokenId) == 
    LET ID == <<classId, tokenId>> IN
    IF ID \in DOMAIN accounts
    THEN accounts[ID]
    ELSE nullAccount

Transfer(classId, tokenIds, receiver) == 
    /\ \A tokenId \in tokenIds: 
        LET ID == <<classId, tokenId>> IN
        /\ ID \in DOMAIN accounts
        /\ accounts[ID] /= receiver
    /\ accounts' = [account \in DOMAIN accounts |->
                        IF account[1] = classId /\ account[2] \in tokenIds
                        THEN receiver
                        ELSE accounts[account]]

Burn(classId, tokenIds) ==
    /\ \A tokenId \in tokenIds: 
        LET ID == <<classId, tokenId>> IN
        /\ ID \in DOMAIN accounts
    /\ accounts' = [account \in DOMAIN accounts \ {<<classId, y>>: y \in tokenIds}|->
                        accounts[account]]

Mint(classId, tokenIds, receiver) == 
    /\ \A tokenId \in tokenIds: 
        LET ID == <<classId, tokenId>> IN
        /\ ID \notin DOMAIN accounts
    /\ accounts' = [account \in DOMAIN accounts \union {<<classId, y>>: y \in tokenIds} |->
                        IF account[1] = classId /\ account[2] \in tokenIds
                        THEN receiver
                        ELSE accounts[account]]

createOutgoingPacket(classId, tokenIds, sender, receiver, sourcePort, sourceChannel) == 
    LET
        source == ~isPrefixMatch(classId, sourcePort, sourceChannel)
        escrowAccount == getChannelEscrowAddresses(sourceChannel)
        data == NonFungibleTokenPacketData(classId, tokenIds, sender, receiver) 
        seq == getNextSeqSend(sourcePort, sourceChannel)
        escrowLog  == LogEntry(sender, sourceChannel, seq, "escrow")
        burnLog  == LogEntry(sender, sourceChannel, seq, "burn")
    IN 
    /\ All({getOwner(classId, tokenId) = sender : tokenId \in tokenIds})
    /\ 
        \/ 
            /\ source
            /\ Transfer(classId, tokenIds, escrowAccount)
            /\ packetLog' = Append(packetLog, escrowLog)
        \/
            /\ ~source
            /\ Burn(classId, tokenIds)
            /\ packetLog' = Append(packetLog, burnLog)
    /\ sendPacket(sourcePort, sourceChannel, data)

onRecvPacket(packet) == 
    LET 
        data == packet.data 
        source == isPrefixMatch(data.classId, packet.sourcePort, packet.sourceChannel)
        slicedClassId == SubSeq(data.classId, 2, Len(data.classId))
        prefixedClassId == <<packet.destChannel>> \o data.classId
        withdrawLog  == LogEntry(data.sender, packet.sourceChannel, packet.sequence, "withdraw")
        mintLog  == LogEntry(data.sender, packet.sourceChannel, packet.sequence, "mint")
    IN 
    /\ 
        \/ 
            /\ source
            /\ Transfer(slicedClassId, data.tokenIds, data.receiver)
            /\ packetLog' = Append(packetLog, withdrawLog)
        \/ 
            /\ ~source
            /\ Mint(prefixedClassId, data.tokenIds, data.receiver)
            /\ packetLog' = Append(packetLog, mintLog)

refundTokens(packet) == 
    LET 
        data == packet.data
        source == ~isPrefixMatch(data.classId, packet.sourcePort, packet.sourceChannel)
        escrowAccount == getChannelEscrowAddresses(packet.sourceChannel)
        log == LogEntry(data.sender, packet.sourceChannel, packet.sequence, "refund")
    IN
    /\ 
        \/ 
            /\ source
            /\ Transfer(data.classId, data.tokenIds, data.sender)
        \/ 
            /\ ~source
            /\ Mint(data.classId, data.tokenIds, data.sender)
    /\ packetLog' = Append(packetLog, log)

HandleRecvPacketandWriteAcknowledgement(packet, proof) == 
    LET 
        sourcePort == packet.sourcePort
        sourceChannel == packet.sourceChannel
        destPort == packet.destPort 
        destChannel == packet.destChannel
        sequence == packet.sequence 
        data == packet.data
        channel == getChannelEnd(destPort, destChannel)
        connection == getConnection(channel.connectionID)
        successReceipt == Receipt(destPort, destChannel, sequence, "SUCCESS")
        receipt == getPacketReceipt(destPort, destChannel, sequence)
        failureAck == Ack(destPort, destChannel, sequence, "failure")
        successAck == Ack(destPort, destChannel, sequence, "success")
    IN 
    /\ channel /= nullChannelEnd
    /\ channel.state = "OPEN"
    /\ sourcePort = channel.counterpartyPortID
    /\ sourceChannel = channel.counterpartyChannelID
    /\ connection /= nullConnectionEnd
    /\ connection.state = "OPEN"
    /\ verifyPacketData(proof, sourcePort, sourceChannel, sequence, data)
    /\ channel.order = "UNORDERED"
    /\ ~isRecvTimeout(sequence)
    /\ receipt = nullReceipt
    /\
        \/ 
            /\ chainStore' = [chainStore EXCEPT 
                                    !.receipts = [chainStore.receipts EXCEPT ![destChannel] = @ \union {successReceipt}],
                                    !.acks = [chainStore.acks EXCEPT ![destChannel] = @ \union {successAck}]]   
            /\ onRecvPacket(packet) 
        \/ 
            /\ chainStore' = [chainStore EXCEPT 
                                    !.receipts = [chainStore.receipts EXCEPT ![destChannel] = @ \union {successReceipt}],
                                    !.acks = [chainStore.acks EXCEPT ![destChannel] = @ \union {failureAck}]] 
            /\ UNCHANGED accounts
            /\ UNCHANGED packetLog

HandleAcknowledgePacket(packet, ack, proof) == 
    LET 
        sourcePort == packet.sourcePort
        sourceChannel == packet.sourceChannel
        destPort == packet.destPort 
        destChannel == packet.destChannel
        sequence == packet.sequence 
        data == packet.data
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        commit == getPacketCommit(sourcePort, sourceChannel, sequence)
    IN     
    /\ channel /= nullChannelEnd
    /\ channel.state = "OPEN"
    /\ destPort = channel.counterpartyPortID
    /\ destChannel = channel.counterpartyChannelID
    /\ connection /= nullConnectionEnd
    /\ connection.state = "OPEN"
    /\ commit = Commit(sourcePort, sourceChannel, sequence, data)
    /\ verifyPacketAck(proof, destPort, destChannel, sequence, ack)
    /\ channel.order = "UNORDERED"
    /\ 
        \/ 
            /\ ack.state = "success" 
            /\ UNCHANGED <<accounts, packetLog>>
        \/ 
            \*/\ ack.state = "failure"
            /\ ack.state /= "success" 
            /\ refundTokens(packet)    
    /\ chainStore' = [chainStore EXCEPT
                                !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]  

HandleTimeoutPacket(packet, proof, nextSeqRecv) ==
    LET 
        sourcePort == packet.sourcePort
        sourceChannel == packet.sourceChannel
        destPort == packet.destPort 
        destChannel == packet.destChannel
        sequence == packet.sequence 
        data == packet.data
        channel == getChannelEnd(sourcePort, sourceChannel)
        connection == getConnection(channel.connectionID)
        commit == getPacketCommit(sourcePort, sourceChannel, sequence)      
    IN 
    /\ channel /= nullChannelEnd
    /\ destChannel = channel.counterpartyChannelID
    /\ destPort = channel.counterpartyPortID 
    /\ isSendTimeout(sequence)
    /\ commit = Commit(sourcePort, sourceChannel, sequence, data)
    /\ channel.order = "UNORDERED"
    /\ verifyPacketReceiptAbsence(proof, destPort, destChannel, sequence)
    /\ chainStore' = [chainStore EXCEPT
                                    !.commitments = [chainStore.commitments EXCEPT ![sourceChannel] = @ \ {commit}]]
    /\ refundTokens(packet)


Actions(port, channel, counterpartyPort, counterpartyChannel, sequence, nextSeqRecv, ack, proof, classId, tokenIds) == 
    LET 
        sendData == NonFungibleTokenPacketData(classId, tokenIds, chainID, counterpartyChainID)
        sendpacket == Packet(sequence, port, channel, counterpartyPort, counterpartyChannel, sendData)
        recvData == NonFungibleTokenPacketData(classId, tokenIds, counterpartyChainID, chainID)
        recvpacket == Packet(sequence, counterpartyPort, counterpartyChannel, port, channel, recvData)
    IN
    /\
        \/ createOutgoingPacket(classId, tokenIds, chainID, counterpartyChainID, port, channel)
        \/ HandleRecvPacketandWriteAcknowledgement(recvpacket, proof)
        \/ HandleAcknowledgePacket(sendpacket, ack, proof)
        \/ HandleTimeoutPacket(sendpacket, proof, nextSeqRecv)
    /\ UNCHANGED packetIsTimeout

======