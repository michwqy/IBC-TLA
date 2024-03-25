-----MODULE Enviroment----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS MaxSeq, MaxAmount, nativeDenominationA, nativeDenominationB, MaxID, EscrowAddress

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
                nativeDenomination <- nativeDenominationA,
                packetLog <- packetLogA

ChainB == INSTANCE Chain 
            WITH chainID <- "chainB",
                counterpartyChainID <- "chainA",
                chainStore <- chainStoreB,
                accounts <- accountsB,
                packetIsTimeout <- packetIsTimeOut,
                nativeDenomination <- nativeDenominationB,
                packetLog <- packetLogB

FungibleTokenPacketData(denomination, amount, sender, receiver) ==
    [
        deno |-> denomination,
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

ChainIDs == {"chainA", "chainB"}
Channels == <<"ch1","ch2","ch3">>
Ports == <<"p1","p2","p3">>

Seqs == 1..MaxSeq
ChannelIDs == {Channels[x] : x \in 1..MaxID}
PortIDs == {Ports[x] : x \in 1..MaxID}

NativeDenos == {nativeDenominationA, nativeDenominationB}  
LimitDenominations ==  {<<nativeDenominationA>>, <<nativeDenominationB>>} \union (ChannelIDs \X NativeDenos) \union (ChannelIDs \X ChannelIDs \X NativeDenos) \union (ChannelIDs \X ChannelIDs \X ChannelIDs \X NativeDenos) 

MaxLogID == 2*2*MaxID*MaxSeq

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
        sender |-> "none",
        sourceChannel |-> nullChannelID,
        sequence |-> nullSeq,
        type |-> "none"
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

getNativeDeno(chainID) == 
    IF chainID = "chainA"
    THEN nativeDenominationA
    ELSE nativeDenominationB

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

getNativeTokens(chainID) ==
    LET accounts == getAccounts(chainID) IN 
    LET nativeTokenSet == { y \in DOMAIN accounts: y[2][1] = getNativeDeno(chainID) } IN
    LET nativeTokenSeq == SetToSeq(nativeTokenSet) IN
    [ x \in 1..Len(nativeTokenSeq) |-> accounts[nativeTokenSeq[x]]]

getEscrowTokens(chainID, deno) ==
    LET accounts == getAccounts(chainID) IN 
    LET escrowTokenSet == { y \in DOMAIN accounts: y[1] = getChannelEscrowAddresses(chainID) /\ y[2] = deno} IN
    LET escrowTokenSeq == SetToSeq(escrowTokenSet) IN
    [ x \in 1..Len(escrowTokenSeq) |-> accounts[escrowTokenSeq[x]]]

getVouchers(chainID, deno) ==
    LET accounts == getAccounts(chainID) IN 
    LET voucherTokenSet == { y \in DOMAIN accounts: (Len(y[2]) = Len(deno)+1) /\ SubSeq(y[2], 1+Len(y[2])-Len(deno), Len(y[2])) = deno } IN
    LET voucherTokenSeq == SetToSeq(voucherTokenSet) IN
    [ x \in 1..Len(voucherTokenSeq) |-> accounts[voucherTokenSeq[x]]]

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
        version |-> "ics20"       
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

Init == 
    /\ chainStoreA = InitChainStore
    /\ accountsA = [<<x,y>> \in { <<z, <<nativeDenominationA>> >> : z \in {"chainA"}} |-> MaxAmount]
    /\ chainStoreB = InitChainStore
    /\ accountsB = [<<x,y>> \in { <<z, <<nativeDenominationB>> >> : z \in {"chainB"}} |-> MaxAmount]
    /\ packetIsTimeOut \in InitIsTimeout
    /\ packetLogA = <<>>
    /\ packetLogB = <<>>

Next == 
    \/ \E chainID \in ChainIDs, 
            sequence, nextSeqRecv \in Seqs,
            channel \in ChannelIDs,
            denomination \in {x[2] : x \in DOMAIN accountsA} \union {x[2]: x \in DOMAIN accountsB}, 
            amount \in 1..MaxAmount:
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
            /\ ChainA!Actions(port, channel, counterpartyPort, counterpartyChannel, sequence, nextSeqRecv, ack, proof, denomination, amount)
            /\ UNCHANGED chainVarsB
        ELSE  
            /\ ChainB!Actions(port, channel, counterpartyPort, counterpartyChannel, sequence, nextSeqRecv, ack, proof, denomination, amount)
            /\ UNCHANGED chainVarsA
    \/ UNCHANGED vars

Fairness == 
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

NonInflationary == 
    \A chainID \in ChainIDs:
        [] (SumSeq(getNativeTokens(chainID)) = MaxAmount )

PegConstraint == 
    \A chainID \in ChainIDs, deno \in LimitDenominations:
        LET 
            counterpartyChainID == getCounterpartyChainID(chainID)
        IN
        /\ [] <> (SumSeq(getEscrowTokens(chainID, deno)) = SumSeq(getVouchers(counterpartyChainID, deno))) 
        /\ [] (SumSeq(getEscrowTokens(chainID, deno)) >= SumSeq(getVouchers(counterpartyChainID, deno)))  

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
    \*/\ [] ((burn \in logset) => <> (refund \in logset \/ withdraw \in counterpartyLogset))
    \*/\ [] ((escrow \in logset ) => <> (refund \in logset \/ mint \in counterpartyLogset))
 
RefundConstraint == 
    \A chainID \in ChainIDs, sequence \in Seqs, channelID \in ChannelIDs:
    LET 
        counterpartyChainID == getCounterpartyChainID(chainID)
        logs == {getPacketLog(chainID)[i]: i \in DOMAIN getPacketLog(chainID)}
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
    \*/\ [] (( (ack = Ack) \/ ( isTimeout(chainID, sequence) /\ commit /= nullCommit ) ) => <> (log \in logs) )


Pro ==
    /\ NonInflationary
    /\ PegConstraint
    /\ RefundConstraint
    /\ Correctness

======