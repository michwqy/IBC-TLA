------- MODULE Chain --------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS chainID, nativeDenomination, MaxSeq, MaxAmount, counterpartyChainID, MaxID, EscrowAddress

VARIABLES chainStore, packetIsTimeout, accounts, packetLog

Packet(sequence, sourcePort, sourceChannel, destPort, destChannel, data) == 
    [
        sequence |-> sequence,
        sourcePort |-> sourcePort,
        sourceChannel |-> sourceChannel,
        destPort |-> destPort,
        destChannel |-> destChannel,
        data |-> data
    ]

FungibleTokenPacketData(denomination, amount, sender, receiver) ==
    [
        denom |-> denomination,
        amount |-> amount,
        sender |-> sender,
        receiver |-> receiver
    ]

nullData ==
    [
        deno |-> <<>>,
        amount |-> 0,
        sender |-> "",
        receiver |-> ""        
    ]

isPrefixMatch(denomination, sourcePort, sourceChannel) ==
    IF Len(denomination) < 2 \/ denomination[1] /= sourceChannel
    THEN FALSE
    ELSE TRUE

getChannelEscrowAddresses(channelID) == 
    EscrowAddress

   
\* packet
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

\* FungibleToken
TransferCoins(sender, receiver, denomination, amount) == 
    LET 
        senderID == <<sender, denomination>>
        receiverID == <<receiver, denomination>>
    IN 
    /\ sender /= receiver
    /\ senderID \in DOMAIN accounts
    /\ accounts[senderID] >= amount
    /\
        \/ 
            /\ receiverID \in DOMAIN accounts
            /\ accounts' = [accounts EXCEPT ![senderID]=@-amount, ![receiverID]=@+amount]
        \/
            /\ receiverID \notin DOMAIN accounts
            /\ accounts' = [account \in DOMAIN accounts \union {receiverID} |->
                                IF account = receiverID
                                THEN amount
                                ELSE 
                                    IF account = senderID
                                    THEN accounts[account]-amount
                                    ELSE accounts[account]]

BurnCoins(sender, denomination, amount) ==
    LET 
        senderID == <<sender, denomination>>
    IN
    /\ senderID \in DOMAIN accounts
    /\ accounts[senderID] >= amount
    /\ accounts' = [accounts EXCEPT ![senderID]=@-amount]

MintCoins(receiver, denomination, amount) == 
    LET 
        receiverID == <<receiver, denomination>>
    IN
    /\ 
        \/ 
            /\ receiverID \in DOMAIN accounts
            /\ accounts' = [accounts EXCEPT ![receiverID]=@+amount]
        \/
            /\ receiverID \notin DOMAIN accounts
            /\ accounts' = [account \in DOMAIN accounts \union {receiverID} |->
                                IF account = receiverID
                                THEN amount
                                ELSE accounts[account]]

sendFungibleTokens(denomination, amount, sender, receiver, sourcePort, sourceChannel) == 
    LET
        escrowAccount == getChannelEscrowAddresses(sourceChannel)
        data == FungibleTokenPacketData(denomination, amount, sender, receiver)
        seq == getNextSeqSend(sourcePort, sourceChannel)
        escrowLog  == LogEntry(sender, sourceChannel, seq, "escrow")
        burnLog  == LogEntry(sender, sourceChannel, seq, "burn")
    IN 
    /\
        \/ 
            /\ ~isPrefixMatch(denomination, sourcePort, sourceChannel)
            /\ TransferCoins(sender, escrowAccount, denomination, amount)
            /\ packetLog' = Append(packetLog, escrowLog)
        \/
            /\ isPrefixMatch(denomination, sourcePort, sourceChannel)
            /\ BurnCoins(sender, denomination, amount)
            /\ packetLog' = Append(packetLog, burnLog)
    /\ sendPacket(sourcePort, sourceChannel, data)

onRecvPacket(packet) == 
    LET 
        data == packet.data 
        escrowAccount == getChannelEscrowAddresses(packet.destChannel)
        slicedDenomination == SubSeq(data.denom, 2, Len(data.denom))
        prefixedDenomination == <<packet.destChannel>> \o data.denom
        withdrawLog  == LogEntry(data.sender, packet.sourceChannel, packet.sequence, "withdraw")
        mintLog  == LogEntry(data.sender, packet.sourceChannel, packet.sequence, "mint")
    IN 
    /\ 
        \/ 
            /\ isPrefixMatch(data.denom, packet.sourcePort, packet.sourceChannel)
            /\ TransferCoins(escrowAccount, data.receiver, slicedDenomination, data.amount)
            /\ packetLog' = Append(packetLog, withdrawLog)
        \/ 
            /\ ~isPrefixMatch(data.denom, packet.sourcePort, packet.sourceChannel)
            /\ MintCoins(data.receiver, prefixedDenomination, data.amount)
            /\ packetLog' = Append(packetLog, mintLog)

refundTokens(packet) == 
    LET 
        data == packet.data
        escrowAccount == getChannelEscrowAddresses(packet.sourceChannel)
        log == LogEntry(data.sender, packet.sourceChannel, packet.sequence, "refund")
    IN
    /\ 
        \/ 
            /\ ~isPrefixMatch(data.denom, packet.sourcePort, packet.sourceChannel)
            /\ TransferCoins(escrowAccount, data.sender, data.denom, data.amount)
        \/
            /\ isPrefixMatch(data.denom, packet.sourcePort, packet.sourceChannel)
            /\ MintCoins(data.sender, data.denom, data.amount)  
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
    /\ commit = Commit(sourcePort, sourceChannel, sequence, data) \*fix
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


Actions(port, channel, counterpartyPort, counterpartyChannel, sequence, nextSeqRecv, ack, proof, denomination, amount) == 
    LET 
        sendData == FungibleTokenPacketData(denomination, amount, chainID, counterpartyChainID)
        sendpacket == Packet(sequence, port, channel, counterpartyPort, counterpartyChannel, sendData)
        recvData == FungibleTokenPacketData(denomination, amount, counterpartyChainID, chainID)
        recvpacket == Packet(sequence, counterpartyPort, counterpartyChannel, port, channel, recvData)
    IN
    /\
        \/ sendFungibleTokens(denomination, amount, chainID, counterpartyChainID, port, channel)
        \/ HandleRecvPacketandWriteAcknowledgement(recvpacket, proof)
        \/ HandleAcknowledgePacket(sendpacket, ack, proof)
        \/ HandleTimeoutPacket(sendpacket, proof, nextSeqRecv)
    /\ UNCHANGED packetIsTimeout

======