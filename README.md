# ibc-tla
This is the public code of paper *Formal Analysis of IBC Protocol* of ICNP 2023
### ICS03
see /ICS03
### ICS04
see /ICS04
### Findings
#### Question 1

>Acknowledging packets is not required

Though it seems that the sent packet may not require an ack, I think that ```acknowledgePacket```, ```timeoutPacket``` and ```timeoutOnClose```  should make every packet sent eventually be ack or timeout in any case (at least at the logical level).

Assume that module a on chain A sends a packet to module b on chain B (by calling ```sendPacket``` and assume that the channel is already open in both chains), and module b receives the packet successfully (by calling ```recvPacket```), then module b closes the channel (by calling ```chanCloseInit```). Now module a has two datagrams on the way and two function ```acknowledgePacket``` and ```chanCloseConfirm``` to call. If ```chanCloseConfirm``` is called first due to the concurrency between relayers or incorrect behavior of relay (the relay is not trusted), ```acknowledgePacket``` can not be called bacause the channel is closed.
```javascript
function acknowledgePacket(
  packet: OpaquePacket,
  acknowledgement: bytes,
  proof: CommitmentProof,
  proofHeight: Height,
  relayer: string): Packet {
    ...
    channel = provableStore.get(channelPath(packet.sourcePort, packet.sourceChannel))
    abortTransactionUnless(channel !== null)
    abortTransactionUnless(channel.state === OPEN)
    ...
  }
```
And the packet can't be ack or timeout (since it has been received successfully).

#### Question 2

I found a logical problem, but I'm not sure if it works in reality. (Some mistakes are possible but may not practical.)

As ICS04, A module can call ```sendPacket``` before a channel open. 
```javascript
function sendPacket(
  capability: CapabilityKey,
  sourcePort: Identifier,
  sourceChannel: Identifier,
  timeoutHeight: Height,
  timeoutTimestamp: uint64,
  data: bytes): uint64 {
    ...
    abortTransactionUnless(channel !== null)
    abortTransactionUnless(channel.state !== CLOSED)
    ...
  }
```
Assume the module successively calls ```chanOpenInit```, ```sendPacket``` and ```chanCloseInit```, which results that there is a in-flight packet and the closed channel.

The module can't call ```timeoutOnClose``` since there is no counterparty channel.
```javascript
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
I think it does not match what the ```timeoutOnClose``` is designed for and 
>Any in-flight packets can be timed-out as soon as a channel is closed

Now we want to use ```timeoutPacket``` to remedy it.

It doesn't matter that it has some problems (As #965). It needs to call ```verifyNextSequenceRecv```, ```verifyPacketReceiptAbsence``` and ```verifyPacketReceipt``` anyway.
```javascript
function timeoutPacket(
  packet: OpaquePacket,
  proof: CommitmentProof,
  proofHeight: Height,
  nextSequenceRecv: Maybe<uint64>,
  relayer: string): Packet {
    ...
    abortTransactionUnless(packet.destChannel === channel.counterpartyChannelIdentifier)
    ...
    abortTransactionUnless(connection.verifyNextSequenceRecv(
          proofHeight,
          proof,
          packet.destPort,
          packet.destChannel,
          nextSequenceRecv
        ))
    ...
    abortTransactionUnless(connection.verifyPacketReceiptAbsence(
          proofHeight,
          proof,
          packet.destPort,
          packet.destChannel,
          packet.sequence
        ))
    ...
    abortTransactionUnless(connection.verifyPacketReceipt(
          proofHeight,
          proof,
          packet.destPort,
          packet.destChannel,
          packet.sequence
          TIMEOUT_RECEIPT,
        ))        
  }
```
I don't know if there functions work properly when ```channel.counterpartyChannelIdentifier``` is empty.

And in [ibc-go](https://github.com/michwqy/ibc-go/blob/main/modules/core/04-channel/keeper/timeout.go), ```TimeoutPacket``` can't be called when channel is closed.
```go
func (k Keeper) TimeoutPacket(
	ctx sdk.Context,
	packet exported.PacketI,
	proof []byte,
	proofHeight exported.Height,
	nextSequenceRecv uint64,
) error {
	if channel.State != types.OPEN {
		return errorsmod.Wrapf(
			types.ErrInvalidChannelState,
			"channel state is not OPEN (got %s)", channel.State.String(),
		)
	}    
}
``` 
#### Question 3
According to 
```javascript
function recvPacket(
  packet: OpaquePacket,
  proof: CommitmentProof,
  proofHeight: Height,
  relayer: string): Packet {
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
```
As for ```packet```, there are three scenarios (assume that all previous packets were successfully received).

- Function ```recvPacket``` has not been called. So ```nextSequenceRecv  == packet.sequence``` whether timeout height/timestamp has passed on the counterparty chain or not.
- Function ```recvPacket``` has been called and timeout height/timestamp has passed on the counterparty chain. So ```nextSequenceRecv  == packet.sequence +1 ``` and ```verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT)) == True```
- Function ```recvPacket``` has been called and timeout height/timestamp has not passed on the counterparty chain. So ```nextSequenceRecv  == packet.sequence +1 ``` and ```verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT)) == False```

So in ```ORDERED_ALLOW_TIMEOUT``` channel, a module can claim a packet is timeout if 
```javascript
nextSequenceRecv  == packet.sequence
```
 means function ```recvPacket``` has not been called.
or 
```javascript
(nextSequenceRecv  == packet.sequence + 1) &&  (verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT)) == True)
``` 
means function ```recvPacket``` has been called and timeout height/timestamp has passed.
But in
```javascript
function timeoutPacket(
  packet: OpaquePacket,
  proof: CommitmentProof,
  proofHeight: Height,
  nextSequenceRecv: Maybe<uint64>,
  relayer: string): Packet {

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
```
I think it means 
```
(nextSequenceRecv  == packet.sequence) &&  (verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT) == True)
```
It may be a mistake. The right one should be 
```
(nextSequenceRecv  <= packet.sequence) || (verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT) == True)
```

And in
```javascript
function timeoutOnClose(
  packet: Packet,
  proof: CommitmentProof,
  proofClosed: CommitmentProof,
  proofHeight: Height,
  nextSequenceRecv: Maybe<uint64>,
  relayer: string): Packet {
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
As
> The timeoutOnClose function is called by a module in order to prove that the channel to which an unreceived packet was addressed has been closed, so the packet will never be received (even if the timeoutHeight or timeoutTimestamp has not yet been reached).

I don't know if the function ```timeoutOnClose``` is allowed to called if timeoutHeight or timeoutTimestamp has been reached. (Like channel is closed after ```recvPacket``` called on counterparty chain and before ```timeoutOnClose``` called on local chain). But If the answer is yes, the condition should be 
```
(nextSequenceRecv <= packet.sequence) || (verifyPacketReceipt(...packet.sequence, TIMEOUT_RECEIPT) == True)
```
#### Question 4

For ```ORDERED_ALLOW_TIMEOUT``` channel, ```timeoutPacket``` will increase ```nextSequenceAck```. 
```javascript
function timeoutPacket(
  packet: OpaquePacket,
  proof: CommitmentProof,
  proofHeight: Height,
  nextSequenceRecv: Maybe<uint64>,
  relayer: string): Packet {
    ...
    if channel.order === ORDERED_ALLOW_TIMEOUT {
      nextSequenceAck = nextSequenceAck + 1
      provableStore.set(nextSequenceAckPath(packet.srcPort, packet.srcChannel), nextSequenceAck)
    }
    ...
  }
```
Assume that module A sent two packets (e.g. sequences are 1,2 and the init ```nextSequenceAck == 1```) and module B received No. 1 packet successfully. But No. 2 packet was timeout and module A called ```timeoutPacket``` for it, which caused the ```nextSequenceAck == 2```. And now module A can't call ```acknowledgePacket``` for No.1 packet, because ```acknowledgePacket``` requires ```packet.sequence === nextSequenceAck```.
```javascript
function acknowledgePacket(
  packet: OpaquePacket,
  acknowledgement: bytes,
  proof: CommitmentProof,
  proofHeight: Height,
  relayer: string): Packet {
    ...
    if (channel.order === ORDERED || channel.order == ORDERED_ALLOW_TIMEOUT) {
      nextSequenceAck = provableStore.get(nextSequenceAckPath(packet.sourcePort, packet.sourceChannel))
      abortTransactionUnless(packet.sequence === nextSequenceAck)
      ...
    }
    ...
  }
```
