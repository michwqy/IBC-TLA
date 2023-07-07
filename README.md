## IBC-TLA+
This is the public code of paper *Formal Analysis of IBC Protocol* of ICNP 2023. This document mainly introduces the overall framework of the code and explains and reports of the identified problems. At the beginning of our research, the latest commitment was [ref](https://github.com/cosmos/ibc/commit/f4d1578afa51e75f03aec8c0967129a38d424b91), and subsequent commitments were not considered.
### ICS03
#### Chain
##### Description
This module represents the block chain, including the data structures and functions about connection handshake. See ICS03/Chain.tla
##### Data Structure
```json
  "ChainStore":{
    "client":{
      "clientID":"string"
      },
    "connectionEnds":[{
      "state":"string",
      "connectionID":"int",
      "clientID":"string",
      "counterpartyConnectionID":"int",
      "counterpartyClientID":"string",
      "versions":"Set(int)"
    }],
    "nextConnectionID":"int",
    "compatibleVersions":"Set(int)"
  }
```
##### Handle Functions
+ HandleConnOpenInit
+ HandleConnOpenTry
+ HandleConnOpenAck
+ HandleConnOpenConfirm
##### Auxiliary Functions
+ Query Functions
  + getChainStore
  + queryClient
  + queryConnection
  + getCompatibleVersions
+ Others
  + generateID
  + pickVersion
  + verifyConnectionState
#### Environment
##### Description
This module simulates the possible behavior of on-chian users and off-chain relayers by arbitrarily calling the Chain module. See ICS03/Environment.tla
##### Key Function
```TLA+
HandleConnection(chainID) ==
    \E clientID, counterpartyClientID \in ClientIDs, connectionID, counterpartyConnectionID \in ConnectionIDs, version \in (SUBSET Versions \ {{}}): 
        LET 
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
```
### ICS04-Channel
#### Chain
##### Description
This module represents the block chain, including the data structures and functions about channel handshake. See ICS04/channel/Chain.tla
##### Data Structure
```json
  "ChainStore":{
    "client":{
      "clientID":"int"
      },
    "connectionEnds":[{
      "state":"string",
      "connectionID":"int",
      "clientID":"int",
      "counterpartyConnectionID":"int",
      "counterpartyClientID":"int",
      "versions":"Set(int)"
    }],
    "channelEnds":[{
        "portID":"int",
        "channelID":"int",
        "state":"string",
        "order":"string",
        "counterpartyPortID":"int",
        "counterpartyChannelID":"int",
        "connectionID":"int",
        "version":"int"
    }],
    "nextChannelID":"int"
  }
```
##### Handle Functions
+ HandlechanOpenInit
+ HandlechanOpenTry
+ HandlechanOpenAck
+ HandlechanOpenConfirm
+ HandlechanCloseInit
+ HandlechanCloseConfirm
##### Auxiliary Functions
+ Query Functions
  + getChainStore
  + getChannelEnd
  + getConnection
+ Others
  + generateID
  + verifyChannelState
#### Environment
##### Description
This module simulates the possible behavior of on-chian users and off-chain relayers by arbitrarily calling the Chain module. See ICS04/channel/Environment.tla
##### Key Function
```TLA+
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
```
### ICS04-Packet
#### Chain
##### Description
This module represents the block chain, including the data structures and functions about channel handshake and packet delivery. See ICS04/packet/Chain.tla
##### Data Structure
```json
  "ChainStore":{
    "client":{
      "clientID":"int"
      },
    "connectionEnds":[{
      "state":"string",
      "connectionID":"int",
      "clientID":"int",
      "counterpartyConnectionID":"int",
      "counterpartyClientID":"int",
      "versions":"Set(int)"
    }],
    "channelEnds":[{
        "portID":"int",
        "channelID":"int",
        "state":"string",
        "order":"string",
        "counterpartyPortID":"int",
        "counterpartyChannelID":"int",
        "connectionID":"int",
        "version":"int"
    }],
    "nextSequenceSend":["int"],
    "nextSequenceRecv":["int"],
    "nextSequenceAck":["int"],
    "commitments":["Set({'portID':'int','channelID':'int','sequence':'int'})"],
    "receipts":["Set({'portID':'int','channelID':'int','sequence':'int','state':'string'})"],
    "acks":["Set({'portID':'int','channelID':'int','sequence':'int'})"],
    "nextChannelID":"int"
  }
```
##### Handle Functions
+ HandlechanOpenInit
+ HandlechanOpenTry
+ HandlechanOpenAck
+ HandlechanOpenConfirm
+ HandlechanCloseInit
+ HandlechanCloseConfirm
+ HandleSendPacket
+ HandleRecvPacketandWriteAcknowledgement
+ HandleAcknowledgePacket
+ HandleTimeoutPacket
+ HandleTimeoutOnClose
##### Auxiliary Functions
+ Query Functions
  + getChainStore
  + getChannelEnd
  + getConnection
  + getNextSeqSend
  + getNextSeqRecv
  + getNextSeqAck
  + getPacketReceipt
  + getPacketAck
  + getPacketCommit
+ Others
  + generateID
  + verifyChannelState
  + verifyPacketData
  + verifyPacketAck
  + verifyNextSeqRecv
  + verifyPacketReceiptAbsence
  + verifyPacketReceipt
  + isSendTimeout
  + isRecvTimeout
#### Environment
##### Description
This module simulates the possible behavior of on-chian users and off-chain relayers by arbitrarily calling the Chain module. See ICS04/packet/Environment.tla
##### Key Function
```TLA+
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
```
### Results
This section mainly discusses the reasons, triggering paths, repair suggestions of identified problems and community responses to our reports.
#### Connection/Channel Handshake 
##### Problem 1
**Reasons and Triggering Paths**

```typescript
function connOpenInit(...) {
    ...
    identifier = generateIdentifier()
    ...
    connection = ConnectionEnd{...}
    provableStore.set(connectionPath(identifier), connection)
    ...
}
```
```typescript
function connOpenTry(...) {
    ...
    identifier = generateIdentifier()
    ...
    connection = ConnectionEnd{...}
    provableStore.set(connectionPath(identifier), connection)
    ...
}
```
As above, both ```connOpenInit``` and ```connOpenTry``` need to create a new connection end with a new identifier and the allocated connection and and identifiers will not be reallocated. It is acceptable that limited identifiers can only be used to create limited connections. But if ```connOpenInit``` runs out of identifiers, ```connOpenTry``` cannot be executed, and there is no connection that can be established, which is a possible DoS attack. 

For example, both Chain A and Chain B can only allocate one identifier. If both Chain A and Chain B want to establish a connection with the other party by executing the ```connOpenInit```, neither party can execute ```connOpenTry``` to respond to the connection initiated by the other party, resulting in no connection being established. 

**Recommendation and Reports**

The direct method is to allow the use of allocated connection ends to complete connection handshake. For example, if both Chain A and Chain B want to initiate a connection with each other, they should directly use two ```INIT``` state connection ends that have already been created to complete the handshake, instead of creating two more ```TRYOPEN``` state connection ends to complete two handshakes. We do not report this problem because similar solutions have been deprecated due to their complex and error prone processing logic, which can refer to [this](https://github.com/cosmos/ibc/pull/629). Considering the high transaction costs and data representation range on the blockchain, identifiers or other resources may be considered sufficient.

##### Problem 2

**Reasons and Triggering Paths**

A ```INIT``` state connection end of the counterparty chain can be used to create multiple ```TRYOPEN ```state connection ends, because ```connOpenTry``` only verifies the counterparty connection end's state and does not check if it already has a corresponding connection end. However, only one of these ```TRYOPEN``` state connection ends will match the ```INIT``` state connection end in the ```connOpenAck``` because the ```connOpenAck`` will change connection end's state. The remaining connection ends will freeze in their previous states. These frozen ends will interfere with the normal use of users, such as mistakenly executing transactions through these unopened connections/channels, resulting in transaction errors.
```typescript
function connOpenAck(...) {
    ...
    abortTransactionUnless((connection.state === INIT && connection.versions.indexOf(version) !== -1))
    ...
    connection.state = OPEN
    ...
    connection.counterpartyConnectionIdentifier = counterpartyIdentifier
    provableStore.set(connectionPath(identifier), connection)
}
```

**Recommendation and Reports**

There are two ways to solve this problem. One is to determine whether there is a corresponding connection end when executing the ```connOpenTry```, and the other is to allow the closure of connection ends that cannot complete the handshake. However, the former requires traversing existing connection ends, while the latter requires the introduction of new judgment and permission mechanisms. [Similar situations have occurred in the actual use of IBC](https://github.com/cosmos/ibc/issues/635#issuecomment-1013262400), and [some have proposed mechanisms similar to the latter, but they have not been adopted](https://github.com/cosmos/ibc/issues/648).
#### Incorrect design of ordered_allow_timeout channels
##### Problem 3

**Reasons and Triggering Paths**

Ordered_allow_timeout channel is a special channel that allows for timeout situations in ordered transmission. However, there are some errors in determining the timeout condition for this channel type.

According to 
```typescript
function recvPacket(...): {
  ...
      switch channel.order {
  ...
        case ORDERED_ALLOW_TIMEOUT:
          if (getConsensusHeight() >= packet.timeoutHeight && packet.timeoutHeight != 0) || (currentTimestamp() >= packet.timeoutTimestamp && packet.timeoutTimestamp != 0) {
            nextSequenceRecv = nextSequenceRecv + 1
            provableStore.set(nextSequenceRecvPath(packet.destPort, packet.destChannel), nextSequenceRecv)
            provableStore.set(
            packetReceiptPath(packet.destPort, packet.destChannel, packet.sequence),
              TIMEOUT_RECEIPT
            )
          }
          return;
  ...
      }
  ...
      switch channel.order {
  ...
        case ORDERED_ALLOW_TIMEOUT:
          nextSequenceRecv = nextSequenceRecv + 1
          provableStore.set(nextSequenceRecvPath(packet.destPort, packet.destChannel), nextSequenceRecv)
          break;
  ...
  }
}
```
A module can claim a packet is timeout if 
```typescript
nextSequenceRecv  <= packet.sequence
```
 means function ```recvPacket``` has not been called.
or 
```typescript
(nextSequenceRecv  == packet.sequence + 1) &&  (verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT)) == True)
``` 
means function ```recvPacket``` has been called and timeout height/timestamp has passed.
But in
```typescript
function timeoutPacket(...): {

...
    switch channel.order {
...
      case ORDERED_ALLOW_TIMEOUT:
        abortTransactionUnless(nextSequenceRecv == packet.sequence)
        abortTransactionUnless(connection.verifyPacketReceipt(
          proofHeight,
          proof,
          packet.destPort,
          packet.destChannel,
          packet.sequence
          TIMEOUT_RECEIPT,
        ))
        break;
...
    } 
...
}

function timeoutOnClose(...): {
  ...

    if channel.order === ORDERED || channel.order == ORDERED_ALLOW_TIMEOUT {
      abortTransactionUnless(connection.verifyNextSequenceRecv(
        proofHeight,
        proof,
        packet.destPort,
        packet.destChannel,
        nextSequenceRecv
      ))
       abortTransactionUnless(nextSequenceRecv <= packet.sequence)
  ...
  ...
  }
}
```
The right one should be 
```typescript
abortTransactionUnless(nextSequenceRecv  <= packet.sequence) || (verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT) == True)
```
**Recommendation and Reports**

We've reported this problem ([ref](https://github.com/cosmos/ibc/issues/965)) and it's being fixed ([ref](https://github.com/cosmos/ibc/pull/977)).
##### Problem 4
**Reasons and Triggering Paths**

For ```ORDERED_ALLOW_TIMEOUT``` channel, ```timeoutPacket``` will increase ```nextSequenceAck```. 
```typescript
function timeoutPacket(...): {
    ...
    if channel.order === ORDERED_ALLOW_TIMEOUT {
      nextSequenceAck = nextSequenceAck + 1
      provableStore.set(nextSequenceAckPath(packet.srcPort, packet.srcChannel), nextSequenceAck)
    }
    ...
  }
```
Assume that module A sent two packets (e.g. sequences are 1,2 and the init ```nextSequenceAck == 1```) and module B received No. 1 packet successfully. But No. 2 packet was timeout and module A called ```timeoutPacket``` for it, which caused the ```nextSequenceAck == 2```. And now module A can't call ```acknowledgePacket``` for No.1 packet, because ```acknowledgePacket``` requires ```packet.sequence === nextSequenceAck```.
```typescript
function acknowledgePacket(...): {
    ...
    if (channel.order === ORDERED || channel.order == ORDERED_ALLOW_TIMEOUT) {
      nextSequenceAck = provableStore.get(nextSequenceAckPath(packet.sourcePort, packet.sourceChannel))
      abortTransactionUnless(packet.sequence === nextSequenceAck)
      ...
    }
    ...
  }
```

**Recommendation and Reports**

There are different solutions to solve this problem, but if data packets are required to be received and answered in the order they were sent, conditions should be added to ensure that all datagram operations are strictly executed in order.
```typescript
function timeoutPacket(...): {
    ...
    if channel.order === ORDERED_ALLOW_TIMEOUT {
      abortTransactionUnless(nextSequenceAck === packet.sequence)
      nextSequenceAck = nextSequenceAck + 1
      provableStore.set(nextSequenceAckPath(packet.srcPort, packet.srcChannel), nextSequenceAck)
    }
    ...
  }
```
We reported this problem, but the developer think it can be handled by the application ([ref](https://github.com/cosmos/ibc/issues/968#issuecomment-1569206700)). Of course, applications can address this issue in a targeted manner, but application developers may not be aware of the need to specifically address this issue. And this problem is actually due to the protocol not fully implementing its semantics: for ordered channels, packets should be processed strictly in order, and the loose conditions of ```timeoutPacket``` break this strict order.
#### Inappropriate handling of abnormal channel states
##### Problem 5

**Reasons and Triggering Paths**

Assume that module a on chain A sends a packet to module b on chain B (by calling ```sendPacket``` and assume that the channel is already open in both chains), and module b receives the packet successfully (by calling ```recvPacket```), then module b closes the channel (by calling ```chanCloseInit```). Now module a has two datagrams on the way and two function ```acknowledgePacket``` and ```chanCloseConfirm``` to call. If ```chanCloseConfirm``` is called first due to the concurrency between relayers or incorrect behavior of relay (the relay is not trusted), ```acknowledgePacket``` can not be called bacause the channel is closed.
```typescript
function acknowledgePacket(...): {
    ...
    channel = provableStore.get(channelPath(packet.sourcePort, packet.sourceChannel))
    abortTransactionUnless(channel !== null)
    abortTransactionUnless(channel.state === OPEN)
    ...
  }
```
And the packet can't be ack or timeout (since it has been received successfully).

**Recommendation and Reports**

At the protocol level, it is possible to solve this problem by allowing packets to be acknowledged after the channel is closed, but developers believe that such issues should be addressed at the application level ([ref](https://github.com/cosmos/ibc/issues/968#issuecomment-1569206700)).

##### Problem 6

**Reasons and Triggering Paths**

As ICS04, A module can call ```sendPacket``` before a channel open, which is called optimistic sending. 
```typescript
function sendPacket(...): {
    ...
    abortTransactionUnless(channel !== null)
    abortTransactionUnless(channel.state !== CLOSED)
    ...
  }
```
Assume the module successively calls ```chanOpenInit```, ```sendPacket``` and ```chanCloseInit```, which results that there is a in-flight packet and the closed channel.

The module can't call ```timeoutOnClose``` since there is no counterparty channel.
```typescript
function timeoutOnClose(
  packet: Packet,
  proof: CommitmentProof,
  proofClosed: CommitmentProof,
  proofHeight: Height,
  nextSequenceRecv: Maybe<uint64>,
  relayer: string): Packet {
    ...
    expected = ChannelEnd{CLOSED, channel.order, channel.portIdentifier,
                          channel.channelIdentifier, channel.connectionHops.reverse(), channel.version}
    abortTransactionUnless(connection.verifyChannelState(
      proofHeight,
      proofClosed,
      channel.counterpartyPortIdentifier,
      channel.counterpartyChannelIdentifier,
      expected
    ))
    ...    
  }
```
It does not match what the ```timeoutOnClose``` is designed for and 
>Any in-flight packets can be timed-out as soon as a channel is closed

**Recommendation and Reports**

There are different ways to solve this problem. We have reported this issue to the developers, who believe that although there is an issue at the protocol level, optimistic sending has been disabled in practical implementation ([ref](https://github.com/cosmos/ibc/issues/968#issuecomment-1552158823)). In fact, optimistic sending is disabled because similar issues have occurred in practical use ([ref](https://github.com/cosmos/ibc/issues/635#issuecomment-1020318753)). The root cause of these problems is that optimistic sending allows packets to be sent on channels that are not yet open, which may result in the channel being in a state of no counterparty, neither open nor closed, closed, or open. But the two functions ```timeoutOnClose``` and ```timeoutPacket``` fail to cover all situations.



#### Code Redundancy

**Reasons and Triggering Paths**

With protocol updates, some code may no longer be in effect. It may be difficult for manual analysis to discover and verify these redundant codes. But through formal analysis, we can prove that these codes are no longer effective.

For example, the condition in ```pendingDatagrams``` in ICS18 is ```localEnd.state === INIT && (remoteEnd === null || remoteEnd.state === INIT)```. It gives the impression that the ```remoteEnd``` corresponding to ```localEnd``` is determined, which is misleading. Actually, ```counterpartyconnectionIdentifier``` in ```localEnd``` is empty, which means ```remoteEnd``` must be ```null```.

```typescript
function pendingDatagrams(...):{
...
  connections = chain.getConnectionsUsingClient(counterparty)
  for (const localEnd of connections) {
    remoteEnd = counterparty.getConnection(localEnd.counterpartyIdentifier)
    if (localEnd.state === INIT && (remoteEnd === null || remoteEnd.state === INIT))
      counterpartyDatagrams.push(ConnOpenTry{...})
  }
...
}
```

**Recommendation and Reports**

We have reported this kind of problems and it has been fixed (ref [1](https://github.com/cosmos/ibc/issues/960), [2](https://github.com/hyperledger-labs/yui-ibc-solidity/issues/168)).

#### Inconsistent in Documents


**Reasons and Triggering Paths**

Due to the continuous maintenance of protocol documents by multiple individuals, it is inevitable that some inconsistencies or errors may occur. Due to the need for careful review of documents during the formal analysis, it is easier to discover these documents.

For example```ConnOpenInit``` called by ```handleConnOpenInit``` in ICS26 should correspond to ```connOpenInit``` in ICS03.
In ICS03, ```connOpenInit``` takes ```counterpartyPrefix, clientIdentifier, counterpartyClientIdentifier, version``` as parameters.
```typescript
function connOpenInit(
  counterpartyPrefix: CommitmentPrefix,
  clientIdentifier: Identifier,
  counterpartyClientIdentifier: Identifier,
  version: string,
  delayPeriodTime: uint64,
  delayPeriodBlocks: uint64) 
  ```
But in ICS26, ```connOpenInit``` takes ```identifier, desiredCounterpartyIdentifier, clientIdentifier, counterpartyClientIdentifier, version``` as parameters.
```typescript
function handleConnOpenInit(datagram: ConnOpenInit) {
    handler.connOpenInit(
      datagram.identifier,
      datagram.desiredCounterpartyIdentifier,
      datagram.clientIdentifier,
      datagram.counterpartyClientIdentifier,
      datagram.version
    )
}
  ```

**Recommendation and Reports**

We have reported this kind of problems and it has been fixed (ref [1](https://github.com/cosmos/ibc/issues/961), [2](https://github.com/cosmos/ibc/issues/934)).