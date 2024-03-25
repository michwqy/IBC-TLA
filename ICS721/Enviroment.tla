-----MODULE Enviroment----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxSeq, MaxTokenId, nativeClassIdA, nativeClassIdB, MaxID, EscrowAddress

VARIABLES chainStoreA, chainStoreB, packetIsTimeOut, accountsA, accountsB, packetLogA, packetLogB

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN 0 ELSE
  Head(s) + SumSeq(Tail(s))

RECURSIVE SetToSeq(_)
SetToSeq(set) == IF set = {} THEN <<>> ELSE
  LET x == CHOOSE x \in set: TRUE
    IN <<x>> \o SetToSeq(set \ {x})

vars == <<chainStoreA, chainStoreB, packetIsTimeOut, accountsA, accountsB, packetLogA, packetLogB>>

chainVarsA == <<chainStoreA, accountsA, packetLogA>>

chainVarsB == <<chainStoreB, accountsB, packetLogB>>

ChainA == INSTANCE Chain 
            WITH chainID <- "chainA",
                counterpartyChainID <- "chainB",
                chainStore <- chainStoreA,
                accounts <- accountsA,
                packetIsTimeout <- packetIsTimeOut,
                nativeClassId <- nativeClassIdA,
                packetLog <- packetLogA

ChainB == INSTANCE Chain 
            WITH chainID <- "chainB",
                counterpartyChainID <- "chainA",
                chainStore <- chainStoreB,
                accounts <- accountsB,
                packetIsTimeout <- packetIsTimeOut,
                nativeClassId <- nativeClassIdB,
                packetLog <- packetLogB

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

ChainIDs == {"chainA", "chainB"}
Channels == <<"ch1","ch2","ch3">>
Ports == <<"p1","p2","p3">>

Seqs == 1..MaxSeq
ChannelIDs == {Channels[x] : x \in 1..MaxID}
PortIDs == {Ports[x] : x \in 1..MaxID}

NativeClassIds == {nativeClassIdA, nativeClassIdB}  
ClassIds == Seq(ChannelIDs \union NativeClassIds)
\*LimitClassIds ==  {<<nativeClassIdA>>, <<nativeClassIdB>>} \union (ChannelIDs \X NativeClassIds)
LimitClassIds ==  {<<nativeClassIdA>>, <<nativeClassIdB>>} \union (ChannelIDs \X NativeClassIds) \union (ChannelIDs \X ChannelIDs \X NativeClassIds) \union (ChannelIDs \X ChannelIDs \X ChannelIDs \X NativeClassIds) 

nullPortID == "none"
nullOrder == "none"
nullVersion == "none"
nullChannelID == "none"
nullSeq == 0

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
        sequence |-> nullSeq,
        data |-> nullData    
    ]    

nullAck == 
    [
        portID |-> nullPortID,
        channelID |-> nullChannelID,
        sequence |-> nullSeq,
        state |-> "none"    
    ]    

nullLog == 
    [
        sourceChannel |-> nullChannelID,
        sequence |-> nullSeq,
        type |-> "none",
        data |-> nullData
    ]

getChainStore(chainID) == 
    IF chainID = "chainA"
    THEN chainStoreA
    ELSE chainStoreB
        
getCounterpartyChainID(chainID) ==
    IF chainID = "chainA"
    THEN "chainB"
    ELSE "chainA"

getPortID(channelID) == 
    Ports[CHOOSE x \in 1..MaxID: Channels[x] = channelID]

getChannelEnd(chainID, channelID) ==
    LET chainstore == getChainStore(chainID)
        channelEnds == chainstore.channelEnds IN 
    channelEnds[channelID]

getAccounts(chainID) == 
    IF chainID = "chainA"
    THEN accountsA
    ELSE accountsB

getNativeClassId(chainID) == 
    IF chainID = "chainA"
    THEN <<nativeClassIdA>>
    ELSE <<nativeClassIdB>>

getChannelEscrowAddresses(channelID) == 
    EscrowAddress

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

proofPacketState(chainID, portID, channelID, sequence) ==
    LET 
        commit == getPacketCommit(chainID, portID, channelID, sequence)
        ack == getPacketAck(chainID, portID, channelID, sequence)
        receipt == getPacketReceipt(chainID, portID, channelID, sequence)
    IN     
        [
            chainID |-> chainID,
            ack |-> ack,
            commit |-> commit,
            receipt |-> receipt
        ]    

getNFTs(chainID, classId, tokenId) ==
    LET accounts == getAccounts(chainID) IN 
    LET NFTSet == { y \in DOMAIN accounts: y[1] = classId /\ y[2] = tokenId } IN
    LET NFTSeq == SetToSeq(NFTSet) IN
    [ x \in 1..Len(NFTSeq) |-> 1]

getEscrowTokens(chainID, classId, tokenId) ==
    LET accounts == getAccounts(chainID) IN 
    LET escrowTokenSet == { y \in DOMAIN accounts: y[1] = classId /\ y[2] = tokenId /\ accounts[y] = getChannelEscrowAddresses(chainID)} IN
    LET escrowTokenSeq == SetToSeq(escrowTokenSet) IN
    [ x \in 1..Len(escrowTokenSeq) |-> 1]

getVouchers(chainID, classId, tokenId) ==
    LET accounts == getAccounts(chainID) IN 
    LET voucherTokenSet == { y \in DOMAIN accounts: (Len(y[1]) = Len(classId) + 1) /\ SubSeq(y[1], 1+Len(y[1])-Len(classId), Len(y[1])) = classId /\ y[2] = tokenId} IN
    LET voucherTokenSeq == SetToSeq(voucherTokenSet) IN
    [ x \in 1..Len(voucherTokenSeq) |-> 1]

getPacketLog(chainID) == 
    IF chainID = "chainA"
    THEN packetLogA
    ELSE packetLogB

getLogEntry(chainID, idx) == 
    LET logs == getPacketLog(chainID) IN 
    IF idx \in DOMAIN logs
    THEN logs[idx]
    ELSE nullLog

isTimeout(chainID, sequence) == 
    packetIsTimeOut[chainID][sequence]

InitNoTimeout == 
    [
        chainA: [Seqs -> {FALSE} ],
        chainB: [Seqs -> {FALSE} ] 
    ]

InitIsTimeout == 
    [
        chainA: [Seqs -> BOOLEAN ],
        chainB: [Seqs -> BOOLEAN ] 
    ]

InitConnection == 
    [
        state |-> "OPEN",
        connectionID |-> 1,
        clientID |-> 1,
        counterpartyConnectionID |-> 1,
        counterpartyClientID |-> 1,
        versions |-> {1}
    ]

InitChannel(portID, channelID)== 
    [
        portID |-> portID,
        channelID |-> channelID,
        state |-> "OPEN",
        order |-> "UNORDERED",
        counterpartyPortID |-> portID,
        counterpartyChannelID |-> channelID,
        connectionID |-> 1,
        version |-> "ics721"       
    ]

InitChainStore ==
    [
        connections |-> <<InitConnection>>,
        channelEnds |-> [x \in ChannelIDs |-> InitChannel(getPortID(x), x)],
        nextSequenceSend |-> [x \in ChannelIDs |-> 1],
        nextSequenceRecv |-> [x \in ChannelIDs |-> 1],
        nextSequenceAck |-> [x \in ChannelIDs |-> 1],
        commitments |-> [x \in ChannelIDs |-> {}], 
        receipts |-> [x \in ChannelIDs |-> {}],
        acks |-> [x \in ChannelIDs |-> {}]
    ]

TokenIds == 1..MaxTokenId

Init == 
    /\ chainStoreA = InitChainStore
    /\ accountsA = [<<x,y>> \in {<<<<nativeClassIdA>>, z>>: z \in TokenIds} |-> "chainA"]
    /\ chainStoreB = InitChainStore
    /\ accountsB = [<<x,y>> \in {<<<<nativeClassIdB>>, z>>: z \in TokenIds} |-> "chainB"]
    /\ packetIsTimeOut \in InitIsTimeout
    /\ packetLogA = <<>>
    /\ packetLogB = <<>>

Next == 
    \/ \E chainID \in ChainIDs, 
            sequence, nextSeqRecv \in Seqs,
            channel \in ChannelIDs,
            classId \in LimitClassIds,
            tokenIds \in ((SUBSET TokenIds) \ {{}}):
        LET 
            port == getPortID(channel)
            channelEnd == getChannelEnd(chainID, channel)
            counterpartyChannel == channelEnd.counterpartyChannelID
            counterpartyPort == channelEnd.counterpartyPortID
            counterpartyChainID == getCounterpartyChainID(chainID)
            ack == getPacketAck(counterpartyChainID, counterpartyPort, counterpartyChannel, sequence)
            proof == proofPacketState(counterpartyChainID, counterpartyPort, counterpartyChannel, sequence)
        IN 
        IF chainID = "chainA"
        THEN  
            /\ ChainA!Actions(port, channel, counterpartyPort, counterpartyChannel, sequence, nextSeqRecv, ack, proof, classId, tokenIds)
            /\ UNCHANGED chainVarsB
        ELSE  
            /\ ChainB!Actions(port, channel, counterpartyPort, counterpartyChannel, sequence, nextSeqRecv, ack, proof, classId, tokenIds)
            /\ UNCHANGED chainVarsA
    \/ UNCHANGED vars

Fairness == 
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeOk == 
    \A chainID \in ChainIDs:
    /\ {x[1]: x \in DOMAIN getAccounts(chainID)} \subseteq ClassIds
    /\ {x[2]: x \in DOMAIN getAccounts(chainID)} \subseteq TokenIds


NonInflationary1 == 
    \A chainID \in ChainIDs, tokenId \in TokenIds:
        /\ [] (SumSeq(getNFTs(chainID, getNativeClassId(chainID), tokenId)) = 1)

NonInflationary2 == 
    \A chainID \in ChainIDs, tokenId \in TokenIds:
        LET 
            classId == getNativeClassId(chainID) 
            counterpartyChainID == getCounterpartyChainID(chainID)
        IN 
        /\ [] (SumSeq(getNFTs(chainID, classId, tokenId)) - SumSeq(getEscrowTokens(chainID, classId, tokenId)) + SumSeq(getVouchers(counterpartyChainID, classId, tokenId)) <= 1)
        /\ [] <> (SumSeq(getNFTs(chainID, classId, tokenId)) - SumSeq(getEscrowTokens(chainID, classId, tokenId)) + SumSeq(getVouchers(counterpartyChainID, classId, tokenId)) = 1)

NonInflationary == 
    /\ NonInflationary1
    \*/\ NonInflationary2

PegConstraint == 
    \A chainID \in ChainIDs, classId \in LimitClassIds, tokenId \in TokenIds:
        LET 
            counterpartyChainID == getCounterpartyChainID(chainID)
        IN
        /\ [] <> (SumSeq(getEscrowTokens(chainID, classId, tokenId)) = SumSeq(getVouchers(counterpartyChainID, classId, tokenId))) 
        /\ [] (SumSeq(getEscrowTokens(chainID, classId, tokenId)) >= SumSeq(getVouchers(counterpartyChainID, classId, tokenId)))  

Correctness == 
    \A chainID \in ChainIDs, channel \in ChannelIDs, seq \in Seqs: 
    LET 
        counterpartyChainID == getCounterpartyChainID(chainID)
        logs == getPacketLog(chainID)
        logset == {logs[i] : i \in DOMAIN logs}
        counterpartyLogset == {getPacketLog(counterpartyChainID)[i] : i \in DOMAIN getPacketLog(counterpartyChainID)}
        escrow == 
            [
                sender |-> chainID,
                sourceChannel |-> channel,
                sequence |-> seq,
                type |-> "escrow"
            ]
        burn == 
            [
                sender |-> chainID,
                sourceChannel |-> channel,
                sequence |-> seq,
                type |-> "burn"
            ]
        refund == 
            [
                sender |-> chainID,
                sourceChannel |-> channel,
                sequence |-> seq,
                type |-> "refund"
            ]
        mint == 
            [
                sender |-> chainID,
                sourceChannel |-> channel,
                sequence |-> seq,
                type |-> "mint"
            ]
        withdraw ==
            [
                sender |-> chainID,
                sourceChannel |-> channel,
                sequence |-> seq,
                type |-> "withdraw"
            ]
    IN
    /\ [] (refund \in logset => (escrow \in logset \/ burn \in logset))
    /\ [] (mint \in logset => escrow \in counterpartyLogset)
    /\ [] (withdraw \in logset => burn \in counterpartyLogset)
    /\ [] ((burn \in logset) => <> (refund \in logset \/ withdraw \in counterpartyLogset))
    /\ [] ((escrow \in logset ) => <> (refund \in logset \/ mint \in counterpartyLogset))
 
RefundConstraint == 
    \A chainID \in ChainIDs, sequence \in Seqs, channelID \in ChannelIDs:
    LET 
        counterpartyChainID == getCounterpartyChainID(chainID)
        logs == {getPacketLog(chainID)[i] : i \in DOMAIN getPacketLog(chainID)}
        channel == getChannelEnd(chainID, channelID)
        portID == channel.portID
        counterpartyChannelID == channel.counterpartyChannelID
        counterpartyPortID == channel.counterpartyPortID
        commit == getPacketCommit(chainID, portID, channelID, sequence)
        log == 
            [
                sender |-> chainID,
                sourceChannel |-> channelID,
                sequence |-> sequence,
                type |-> "refund"
            ]
        ack == 
            [
                portID |-> counterpartyPortID,
                channelID |-> counterpartyChannelID,
                sequence |-> sequence,
                state |-> "failure"  
            ]
        Ack == getPacketAck(counterpartyChainID, counterpartyPortID, counterpartyChannelID, sequence)
    IN
    /\ [] ( (log \in logs) => (ack = Ack) \/ (isTimeout(chainID, sequence)))
    \*/\ [] ( (ack = Ack) \/ ( isTimeout(chainID, sequence) /\ commit /= nullCommit ) => <> (log \in logs) )


Pro ==
    \*/\ NonInflationary
    \*/\ PegConstraint
    /\ RefundConstraint
    \*/\ Correctness

======