------------------------ MODULE Enviroment -------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxChannelID, MaxPortID, MaxSeq, MaxVersion, MaxConnectionID

VARIABLES chainAStore, chainBStore, packetLogA, packetLogB, packetIsTimeOut

vars == <<chainAStore, chainBStore, packetLogA, packetLogB, packetIsTimeOut>>

chainStores == <<chainAStore, chainBStore>>

chainAvars == <<chainAStore, packetLogA>>

chainBvars == <<chainBStore, packetLogB>>

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

\*packet
nullSeq == 0
Seqs == 1..MaxSeq

nullReceipt ==
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq,
        state |-> "none"        
    ]

nullCommit == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq      
    ]    

nullAck == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq      
    ]    
\* chain
ChainIDs == {"chainA", "chainB"}

\* packet log
LogEntry(portID, channelID, seq, type) ==
    [
        portID |-> portID,
        channelID |-> channelID,
        seq |-> seq,
        type |-> type
    ]

nullLogEntry == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        seq |-> nullSeq,
        type |-> "none"       
    ]

ChainA == INSTANCE Chain 
            WITH chainID <- "chainA",
                counterpartyChainID <- "chainB",
                chainStore <- chainAStore,
                packetLog <- packetLogA,
                packetIsTimeout <- packetIsTimeOut

ChainB == INSTANCE Chain 
            WITH chainID <- "chainB",
                counterpartyChainID <- "chainA",
                chainStore <- chainBStore,
                packetLog <- packetLogB,
                packetIsTimeout <- packetIsTimeOut

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

getNextSeqRecv(chainID, portID, channelID) == 
    LET seqRecv == getChainStore(chainID).nextSequenceRecv IN 
    IF channelID \in DOMAIN seqRecv
    THEN seqRecv[channelID]
    ELSE nullSeq

getPacketReceipt(chainID, portID, channelID, sequence) ==
    LET receipts == getChainStore(chainID).receipts IN
    IF channelID \in DOMAIN receipts /\ sequence \in {x.sequence : x \in receipts[channelID]}
    THEN CHOOSE x \in receipts[channelID]: x.sequence = sequence
    ELSE nullReceipt

getPacketAck(chainID, portID, channelID, sequence) ==
    LET acks == getChainStore(chainID).acks IN
    IF channelID \in DOMAIN acks /\ sequence \in {x.sequence : x \in acks[channelID]}
    THEN CHOOSE x \in acks[channelID]: x.sequence = sequence
    ELSE nullAck

getPacketCommit(chainID, portID, channelID, sequence) ==
    LET commits == getChainStore(chainID).commitments IN
    IF channelID \in DOMAIN commits /\ sequence \in {x.sequence : x \in commits[channelID]}
    THEN CHOOSE x \in commits[channelID]: x.sequence = sequence
    ELSE nullCommit

getPacketLog(chainID) == 
    IF chainID = "chainA"
    THEN packetLogA
    ELSE packetLogB

getLogEntry(chainID, portID, channelID, seq) == 
    LET 
        packetLog == getPacketLog(chainID)
        logs == {packetLog[i] : i \in DOMAIN packetLog}
    IN 
    IF portID \in {x.portID: x \in logs} /\ channelID \in {x.channelID: x \in logs} /\ seq \in {x.seq: x \in logs}
    THEN CHOOSE x \in logs: x.portID = portID /\ x.channelID = channelID /\  x.seq = seq
    ELSE nullLogEntry

proofChannelState(chainID, portID, channelID) ==
    LET chainstore == getChainStore(chainID)
        channels == chainstore.channelEnds
    IN
    IF channelID \in DOMAIN channels /\ channels[channelID].portID = portID
    THEN [chainID |-> chainID, channel |-> channels[channelID]]
    ELSE [chainID |-> chainID, channel |-> nullChannelEnd]

proofPacketState(chainID, portID, channelID, sequence) ==
    LET 
        commit == getPacketCommit(chainID, portID, channelID, sequence)
        ack == getPacketAck(chainID, portID, channelID, sequence)
        receipt == getPacketReceipt(chainID, portID, channelID, sequence)
        nextSeqRecv == getNextSeqRecv(chainID, portID, channelID)
    IN     
        [
            chainID |-> chainID,
            ack |-> ack,
            commit |-> commit,
            receipt |-> receipt,
            nextSeqRecv |-> nextSeqRecv
        ]

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

HandlePacket(chainID) == 
    \E sourcePort, destPort \in PortIDs, sourceChannel, destChannel \in ChannelIDs, sequence, nextSeqRecv \in Seqs:
    LET 
        counterpartyChainID == getCounterpartyChainID(chainID)
        proofSource == proofPacketState(counterpartyChainID, sourcePort, sourceChannel, sequence)
        proofDest == proofPacketState(counterpartyChainID, destPort, destChannel, sequence)
        proofChannel == proofChannelState(counterpartyChainID, destPort, destChannel)
    IN 
    IF chainID = "chainA"
    THEN  
        /\ ChainA!HandlePacket(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proofChannel, proofSource, proofDest)
        /\ UNCHANGED chainBvars
    ELSE  
        /\ ChainB!HandlePacket(sourcePort, sourceChannel, destPort, destChannel, sequence, nextSeqRecv, proofChannel, proofSource, proofDest)
        /\ UNCHANGED chainAvars

InitIsTimeout == 
    [
        chainA: [Seqs -> BOOLEAN ],
        chainB: [Seqs -> BOOLEAN ] 
    ]

Init == 
    /\ ChainA!Init
    /\ ChainB!Init
    /\ packetIsTimeOut \in InitIsTimeout

Next == 
        \/ \E chainID \in ChainIDs: 
            \/ HandleChannel(chainID)
            \/ HandlePacket(chainID)
        \/ UNCHANGED vars

Fairness == 
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOK == 
    /\ ChainA!TypeOK
    /\ ChainB!TypeOK


RecvOrTimeout == 
    \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs, sequence \in Seqs:
        LET 
            send == LogEntry(portID, channelID, sequence, "send") 
            ack == LogEntry(portID, channelID, sequence, "ack") 
            timeout == LogEntry(portID, channelID, sequence, "timeout") 
            close == LogEntry(portID, channelID, sequence, "close")
            packetLog == getPacketLog(chainID)
            logs  == {packetLog[i] : i \in DOMAIN packetLog}
        IN 
            [] ((send \in logs) => <> (ack \in logs \/ timeout \in logs \/ close \in logs))

RecvAfterSend == 
    \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs, sequence \in Seqs:
        LET 
            counterpartyChainID == getCounterpartyChainID(chainID)
            channel == getChannelEnd(chainID, portID, channelID)
            counterpartyPortID == channel.counterpartyPortID
            counterpartyChannelID == channel.counterpartyChannelID
            send == LogEntry(counterpartyPortID, counterpartyChannelID, sequence, "send")
            recv == LogEntry(portID, channelID, sequence, "recv") 
            packetLog == getPacketLog(chainID)
            counterpartyPacketLog == getPacketLog(counterpartyChainID)
            logs  == {packetLog[i] : i \in DOMAIN packetLog}
            counterpartyLogs == {counterpartyPacketLog[i] : i \in DOMAIN counterpartyPacketLog}
        IN 
            [] (recv \in logs => send \in counterpartyLogs)

AckAfterRecv == 
    \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs, sequence \in Seqs:
        LET 
            counterpartyChainID == getCounterpartyChainID(chainID)
            channel == getChannelEnd(chainID, portID, channelID)
            counterpartyPortID == channel.counterpartyPortID
            counterpartyChannelID == channel.counterpartyChannelID
            recv == LogEntry(counterpartyPortID, counterpartyChannelID, sequence, "recv")
            ack == LogEntry(portID, channelID, sequence, "ack") 
            packetLog == getPacketLog(chainID)
            counterpartyPacketLog == getPacketLog(counterpartyChainID)
            logs  == {packetLog[i] : i \in DOMAIN packetLog}
            counterpartyLogs == {counterpartyPacketLog[i] : i \in DOMAIN counterpartyPacketLog}
        IN 
            [] (ack \in logs => recv \in counterpartyLogs)

TimeoutAfterSend == 
    \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs, sequence \in Seqs:
        LET 

            send == LogEntry(portID, channelID, sequence, "send")
            timeout == LogEntry(portID, channelID, sequence, "timeout") 
            close == LogEntry(portID, channelID, sequence, "close") 
            packetLog == getPacketLog(chainID)
            logs  == {packetLog[i] : i \in DOMAIN packetLog}
        IN 
            [] ((close \in logs \/ timeout \in logs) => send \in logs)     

RecvXorTimeout == 
    \A chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs, sequence \in Seqs:
        LET 
            counterpartyChainID == getCounterpartyChainID(chainID)
            channel == getChannelEnd(chainID, portID, channelID)
            counterpartyPortID == channel.counterpartyPortID
            counterpartyChannelID == channel.counterpartyChannelID
            recv == LogEntry(counterpartyPortID, counterpartyChannelID, sequence, "recv")
            ack == LogEntry(portID, channelID, sequence, "ack") 
            timeout == LogEntry(portID, channelID, sequence, "timeout") 
            close == LogEntry(portID, channelID, sequence, "close") 
            packetLog == getPacketLog(chainID)
            counterpartyPacketLog == getPacketLog(counterpartyChainID)
            logs  == {packetLog[i] : i \in DOMAIN packetLog}
            counterpartyLogs == {counterpartyPacketLog[i] : i \in DOMAIN counterpartyPacketLog}
        IN 
            [] ((close \in logs \/ timeout \in logs) => ~(recv \in counterpartyLogs \/ ack \in logs))

OrderedChannel == 
    \A seq \in Seqs, chainID \in ChainIDs, portID \in PortIDs, channelID \in ChannelIDs:
        LET 
            logi == LogEntry(portID, channelID, seq, "recv")
            logj == LogEntry(portID, channelID, seq-1, "recv")
            packetLog == getPacketLog(chainID)
            logs  == {packetLog[i] : i \in DOMAIN packetLog}
            channel == getChannelEnd(chainID, portID, channelID)
        IN 
        [] ((channel.order /= "UNORDERED" /\ logi \in logs /\ seq >1) => (logj \in logs))
          
Pro == 
    \*/\ RecvOrTimeout
    /\ RecvAfterSend
    /\ AckAfterRecv
    /\ TimeoutAfterSend
    /\ RecvXorTimeout
    /\ OrderedChannel
       
=============================================================================