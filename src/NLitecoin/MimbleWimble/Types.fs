namespace NLitecoin.MimbleWimble

open System
open System.IO

open Fsdk.Misc
open NBitcoin
open NBitcoin.Protocol
open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Parameters

type ISerializeable =
    abstract Write: BitcoinStream -> unit
    // no Read() method as it will be static method and can't be included in interface

/// Amount of litecoins in litoshi
type Amount = int64

[<AutoOpen>]
module Helpers =
    let Write (stream: BitcoinStream) (object: #ISerializeable) =
        BetterAssert stream.Serializing "stream.Serializing should be true when writing"
        object.Write stream

    let WriteUint256 (stream: BitcoinStream) (number: uint256) =
        BetterAssert stream.Serializing "stream.Serializing should be true when writing"
        number.AsBitcoinSerializable().ReadWrite stream

    let ReadUint256 (stream: BitcoinStream) : uint256 =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        let tempValue = uint256.MutableUint256()
        tempValue.ReadWrite stream
        tempValue.Value
    
    let ReadArray<'T> (stream: BitcoinStream) (readFunc : BitcoinStream -> 'T) : array<'T> =
        let len = int <| VarInt.StaticRead stream
        Array.init len (fun _ -> readFunc stream)

    let WriteArray<'T when 'T :> ISerializeable> (stream: BitcoinStream) (arr: array<'T>) =
        let len = uint64 arr.Length
        VarInt.StaticWrite(stream, len)
        for each in arr do
            each.Write stream

    let ReadByteArray (stream: BitcoinStream) : array<byte> =
        ReadArray 
            stream 
            (fun s -> 
                s.ReadWrite Unchecked.defaultof<byte>)

    let WriteByteArray (stream: BitcoinStream) (arr: array<byte>) =
        let len = uint64 arr.Length
        VarInt.StaticWrite(stream, len)
        stream.ReadWrite arr

    let ReadAmount (stream: BitcoinStream) : Amount =
        let amountRef = ref 0UL
        stream.ReadWriteAsCompactVarInt amountRef
        amountRef.Value |> int64

    let WriteAmount (stream: BitcoinStream) (amount: Amount) =
        stream.ReadWriteAsCompactVarInt(amount |> uint64 |> ref)

    let ConvertBits (fromBits: int) (toBits: int) (input: array<byte>) : array<byte> =
        let maxV = (1u <<< toBits) - 1u
        let maxAcc = (1u <<< (fromBits + toBits - 1)) - 1u
        [|
            let mutable acc = 0u
            let mutable bits = 0
            for currByte in input do
                acc <- ((acc <<< fromBits) ||| (uint32 currByte)) &&& maxAcc
                bits <- bits + fromBits
                while bits >= toBits do
                    bits <- bits - toBits
                    yield byte((acc >>> bits) &&& maxV)
            if bits > 0 then 
                yield byte((acc <<< (toBits - int bits)) &&& maxV)
        |]

type BlindingFactor = 
    | BlindingFactor of uint256
    member self.ToUInt256() =
        match self with
        | BlindingFactor number -> number

    static member Read(stream: BitcoinStream) : BlindingFactor =
        BlindingFactor(ReadUint256 stream)

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | BlindingFactor number -> number |> WriteUint256 stream

type Hash = 
    | Hash of uint256
    member self.ToUInt256() =
        match self with
        | Hash number -> number

    member self.ToBytes() =
        self.ToUInt256().ToBytes()

    static member Read(stream: BitcoinStream) : Hash =
        ReadUint256 stream |> Hash

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | Hash number -> number |> WriteUint256 stream

module internal HashTags =
    let ADDRESS = 'A'
    let BLIND = 'B'
    let DERIVE = 'D'
    let NONCE = 'N'
    let OUT_KEY = 'O'
    let SEND_KEY = 'S'
    let TAG = 'T'
    let NONCE_MASK = 'X'
    let VALUE_MASK = 'Y'

type Hasher(?hashTag: char) =
    let blake3 = Blake3Digest()
    do
        blake3.Init(Blake3Parameters())
        match hashTag with
        | Some tag -> blake3.Update(byte tag)
        | None -> ()

    member _.Write(bytes: array<uint8>) =
        blake3.BlockUpdate(bytes, 0, bytes.Length)

    member self.Append(object: ISerializeable) =
        use stream = new MemoryStream()
        let writer = new BitcoinStream(stream, true)
        object.Write writer
        self.Write(stream.ToArray())

    member _.Hash() =
        let length = 32
        let bytes = Array.zeroCreate length
        blake3.OutputFinal(bytes, 0, length) |> ignore
        Hash(uint256 bytes)

    static member CalculateHash(object: ISerializeable) =
        let hasher = Hasher()
        hasher.Append object
        hasher.Hash()

type BigInt(bytes: array<byte>) =
    member _.Data = bytes

    interface IEquatable<BigInt> with
        override self.Equals other = self.Data = other.Data
    
    override self.Equals other = 
        match other with
        | :? BigInt as otherBigInt -> self.Data = otherBigInt.Data
        | _ -> false

    override self.GetHashCode() = self.Data.GetHashCode()

    interface IComparable with
        override self.CompareTo other = 
            match other with
            | :? BigInt as otherBigInt -> 
                compare self.Data otherBigInt.Data
            | _ -> failwith "Other is not BigInt"

    override self.ToString() =
        let encoder = NBitcoin.DataEncoders.HexEncoder()
        sprintf "BigInt %s" (encoder.EncodeData bytes)

    static member Read(stream: BitcoinStream) (numBytes: int) : BigInt =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        let result : array<uint8> = Array.zeroCreate numBytes
        stream.ReadWrite result
        BigInt result

    interface ISerializeable with
        member self.Write(stream) =
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"
            stream.ReadWrite self.Data

type PedersenCommitment = 
    | PedersenCommitment of BigInt
    static member NumBytes = 33

    static member Read(stream: BitcoinStream) =
        PedersenCommitment(BigInt.Read stream PedersenCommitment.NumBytes)

    member self.ToBytes() = 
        match self with
        | PedersenCommitment bigint -> bigint.Data

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | PedersenCommitment number -> (number :> ISerializeable).Write stream

type PublicKey = 
    | PublicKey of BigInt
    static member NumBytes = 33

    static member Read(stream: BitcoinStream) =
        PublicKey(BigInt.Read stream PublicKey.NumBytes)

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | PublicKey number -> (number :> ISerializeable).Write stream

    member self.ToBytes() =
        match self with
        | PublicKey bigint -> bigint.Data

type Signature = 
    | Signature of BigInt
    static member NumBytes = 64

    static member Read(stream: BitcoinStream) =
        Signature(BigInt.Read stream Signature.NumBytes)

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | Signature number -> (number :> ISerializeable).Write stream

type InputFeatures =
    | STEALTH_KEY_FEATURE_BIT = 0x01
    | EXTRA_DATA_FEATURE_BIT = 0x02

type OutputFeatures =
    | STANDARD_FIELDS_FEATURE_BIT = 0x01
    | EXTRA_DATA_FEATURE_BIT = 0x02

[<CustomComparison; StructuralEquality>]
type Input =
    {
        Features: InputFeatures
        OutputID: Hash
        Commitment: PedersenCommitment
        InputPublicKey: Option<PublicKey>
        OutputPublicKey: PublicKey
        ExtraData: array<uint8>
        Signature: Signature
    }
    
    static member Read(stream: BitcoinStream) : Input =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        let features = (stream.ReadWrite Unchecked.defaultof<byte>) |> int |> enum<InputFeatures>
        let outputId = Hash.Read stream
        let commitment = PedersenCommitment.Read stream
        let outputPubKey = PublicKey.Read stream

        let inputPubKey =
            if int(features &&& InputFeatures.STEALTH_KEY_FEATURE_BIT) <> 0 then
                Some <| PublicKey.Read stream
            else
                None

        let extraData =
            if int(features &&& InputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                ReadByteArray stream
            else
                Array.empty

        let signature = Signature.Read stream

        let result = 
            {
                Features = features
                OutputID = outputId
                Commitment = commitment
                OutputPublicKey = outputPubKey
                InputPublicKey = inputPubKey
                ExtraData = extraData
                Signature = signature
            }

        result

    interface ISerializeable with
        member self.Write(stream) = 
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"

            stream.ReadWrite (byte self.Features) |> ignore
            Write stream self.OutputID
            Write stream self.Commitment
            Write stream self.OutputPublicKey

            if int(self.Features &&& InputFeatures.STEALTH_KEY_FEATURE_BIT) <> 0 then
                Write stream self.InputPublicKey.Value

            if int(self.Features &&& InputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                WriteByteArray stream self.ExtraData

            Write stream self.Signature

    interface IComparable<Input> with
        member self.CompareTo(other) =
            compare (Hasher.CalculateHash self) (Hasher.CalculateHash other)

    interface IComparable with
        member self.CompareTo(other) =
            match other with
            | :? Input as input -> (self :> IComparable<Input>).CompareTo input
            | _ -> 0

type OutputMessageStandardFields =
    {
        KeyExchangePubkey: PublicKey
        ViewTag: uint8
        MaskedValue: uint64
        MaskedNonce: BigInt
    }
    static member MaskedNonceNumBytes = 16

type OutputMessage =
    {
        Features: OutputFeatures
        StandardFields: Option<OutputMessageStandardFields>
        ExtraData: array<uint8>
    }
    static member Read(stream: BitcoinStream) : OutputMessage =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"

        let featuresByte = stream.ReadWrite Unchecked.defaultof<byte>
        let features = featuresByte |> int |> enum<OutputFeatures>
        
        let standardFields =
            if int(features &&& OutputFeatures.STANDARD_FIELDS_FEATURE_BIT) <> 0 then
                let pubKey = PublicKey.Read stream
                let viewTag = stream.ReadWrite Unchecked.defaultof<byte>
                let maskedValue = stream.ReadWrite Unchecked.defaultof<uint64>
                let maskedNonce = BigInt.Read stream OutputMessageStandardFields.MaskedNonceNumBytes
                {
                    KeyExchangePubkey = pubKey
                    ViewTag = viewTag
                    MaskedValue = maskedValue
                    MaskedNonce = maskedNonce
                }
                |> Some
            else
                None

        let extraData =
            if int(features &&& OutputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                ReadByteArray stream
            else
                Array.empty

        {
            Features = features
            StandardFields = standardFields
            ExtraData = extraData
        }

    interface ISerializeable with
        member self.Write(stream) = 
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"
            
            stream.ReadWrite(self.Features |> uint8) |> ignore

            if int(self.Features &&& OutputFeatures.STANDARD_FIELDS_FEATURE_BIT) <> 0 then
                let fields = self.StandardFields.Value
                Write stream fields.KeyExchangePubkey
                stream.ReadWrite fields.ViewTag |> ignore
                stream.ReadWrite fields.MaskedValue |> ignore
                (fields.MaskedNonce :> ISerializeable).Write stream

            if int(self.Features &&& OutputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                WriteByteArray stream self.ExtraData

type RangeProof =
    | RangeProof of array<uint8>

    static member Size = 675

    static member Read(stream: BitcoinStream) : RangeProof =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        let bytes = Array.zeroCreate<byte> RangeProof.Size
        stream.ReadWrite bytes
        RangeProof bytes

    interface ISerializeable with
        member self.Write(stream) = 
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"
            match self with
            | RangeProof bytes -> 
                BetterAssert (bytes.Length = RangeProof.Size) "incorrect proof size"
                stream.ReadWrite bytes

type StealthAddress =
    {
        ScanPubKey: PublicKey
        SpendPubKey: PublicKey
    }
    interface ISerializeable with
        member self.Write(stream) = 
            (self.ScanPubKey :> ISerializeable).Write stream
            (self.SpendPubKey :> ISerializeable).Write stream

    static member Bech32Prefix = "ltcmweb"
    
    static member DecodeDestination(addressString: string) : StealthAddress =
        let encoder = 
            DataEncoders.Encoders.Bech32(StealthAddress.Bech32Prefix, StrictLength = false)
        let bytes = 
            encoder
                .DecodeDataRaw(addressString, ref DataEncoders.Bech32EncodingType.BECH32)
        use memoryStream = 
            let bitsInByte = 8
            let bitsExpectedByBech32Encoder = 5
            new MemoryStream(bytes |> Array.skip 1 |> ConvertBits bitsExpectedByBech32Encoder bitsInByte)
        let bitcoinStream = new BitcoinStream(memoryStream, false)
        {
            ScanPubKey = PublicKey.Read bitcoinStream
            SpendPubKey = PublicKey.Read bitcoinStream
        }

    member self.EncodeDestination() : string = 
        use memoryStream = new MemoryStream()
        let bitcoinStream = new BitcoinStream(memoryStream, true)
        (self :> ISerializeable).Write bitcoinStream
        let data = 
            let bitsInByte = 8
            let bitsExpectedByBech32Encoder = 5
            Array.append
                (Array.singleton 0uy)
                (memoryStream.ToArray() |> ConvertBits bitsInByte bitsExpectedByBech32Encoder)
        
        DataEncoders.Encoders.Bech32(StealthAddress.Bech32Prefix)
            .EncodeData(data, DataEncoders.Bech32EncodingType.BECH32)

type OutputMask =
    {
        PreBlind: BlindingFactor
        ValueMask: uint64
        NonceMask: BigInt
    }
    static member NonceMaskNumBytes = 16
    
    /// Feeds the shared secret 't' into tagged hash functions to derive:
    ///  q - the blinding factor
    ///  v' - the value mask
    ///  n' - the nonce mask
    static member FromShared (sharedSecret: uint256) =
        let preBlind = 
            let hasher = Hasher(HashTags.BLIND)
            hasher.Write(sharedSecret.ToBytes())
            hasher.Hash().ToUInt256()
            |> BlindingFactor.BlindingFactor
        let valueMask = 
            let hasher = Hasher(HashTags.VALUE_MASK)
            hasher.Write(sharedSecret.ToBytes())
            hasher.Hash().ToBytes() 
            |> Array.take 8 
            |> BitConverter.ToUInt64
        let nonceMask =
            let hasher = Hasher(HashTags.NONCE_MASK)
            hasher.Write(sharedSecret.ToBytes())
            hasher.Hash().ToBytes() 
            |> Array.take OutputMask.NonceMaskNumBytes 
            |> BigInt
        {
            PreBlind = preBlind
            ValueMask = valueMask
            NonceMask = nonceMask
        }

    member self.MaskValue (value: uint64) =
        value ^^^ self.ValueMask

    member self.MaskNonce (nonce: BigInt) =
        Array.map2
            (^^^)
            nonce.Data
            self.NonceMask.Data
        |> BigInt

[<CustomComparison; StructuralEquality>]
type Output =
    {
        Commitment: PedersenCommitment
        SenderPublicKey: PublicKey
        ReceiverPublicKey: PublicKey
        Message: OutputMessage
        RangeProof: RangeProof
        Signature: Signature
    }
    static member Read(stream: BitcoinStream) : Output =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        {
            Commitment = PedersenCommitment.Read stream
            SenderPublicKey = PublicKey.Read stream
            ReceiverPublicKey = PublicKey.Read stream
            Message = OutputMessage.Read stream
            RangeProof = RangeProof.Read stream
            Signature = Signature.Read stream
        }

    interface ISerializeable with
        member self.Write stream = 
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"

            Write stream self.Commitment
            Write stream self.SenderPublicKey
            Write stream self.ReceiverPublicKey
            Write stream self.Message
            Write stream self.RangeProof
            Write stream self.Signature

    interface IComparable<Output> with
        member self.CompareTo other =
            compare (Hasher.CalculateHash self) (Hasher.CalculateHash other)

    interface IComparable with
        member self.CompareTo other =
            match other with
            | :? Output as output -> (self :> IComparable<Output>).CompareTo output
            | _ -> 0

    member self.GetOutputID() : Hash =
        let hasher = Hasher()
        hasher.Append self.Commitment
        hasher.Append self.SenderPublicKey
        hasher.Append self.ReceiverPublicKey
        hasher.Append(Hasher.CalculateHash self.Message)
        hasher.Append(Hasher.CalculateHash self.RangeProof)
        hasher.Append self.Signature
        hasher.Hash()

type KernelFeatures =
    | FEE_FEATURE_BIT = 0x01
    | PEGIN_FEATURE_BIT = 0x02
    | PEGOUT_FEATURE_BIT = 0x04
    | HEIGHT_LOCK_FEATURE_BIT = 0x08
    | STEALTH_EXCESS_FEATURE_BIT = 0x10
    | EXTRA_DATA_FEATURE_BIT = 0x20

module KernelFeatures =
    let ALL_FEATURE_BITS = 
        KernelFeatures.FEE_FEATURE_BIT |||
        KernelFeatures.PEGIN_FEATURE_BIT ||| 
        KernelFeatures.PEGOUT_FEATURE_BIT ||| 
        KernelFeatures.HEIGHT_LOCK_FEATURE_BIT ||| 
        KernelFeatures.STEALTH_EXCESS_FEATURE_BIT ||| 
        KernelFeatures.EXTRA_DATA_FEATURE_BIT

type PegOutCoin =
    {
        Amount: Amount
        ScriptPubKey: NBitcoin.Script // ?
    }
    static member Read(stream: BitcoinStream) : PegOutCoin =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        let amount = ReadAmount stream
        let scriptPubKeyRef = ref NBitcoin.Script.Empty
        stream.ReadWrite scriptPubKeyRef
        {
            Amount = amount
            ScriptPubKey = scriptPubKeyRef.Value
        }

    interface ISerializeable with
        member self.Write(stream) = 
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"
            WriteAmount stream self.Amount
            stream.ReadWrite self.ScriptPubKey |> ignore

[<CustomComparison; StructuralEquality>]
type Kernel =
    {
        Features: KernelFeatures
        Fee: Option<Amount>
        Pegin: Option<Amount>
        Pegouts: array<PegOutCoin>
        LockHeight: Option<int32>
        StealthExcess: Option<PublicKey>
        ExtraData: array<uint8>
        // Remainder of the sum of all transaction commitments. 
        // If the transaction is well formed, amounts components should sum to zero and the excess is hence a valid public key.
        Excess: PedersenCommitment
        // The signature proving the excess is a valid public key, which signs the transaction fee.
        Signature: Signature
    }
    static member Read(stream: BitcoinStream) : Kernel =
        BetterAssert (not stream.Serializing) "stream.Serializing should be false when reading"
        let features = (stream.ReadWrite Unchecked.defaultof<byte>) |> int |> enum<KernelFeatures>

        let fee =
            if int(features &&& KernelFeatures.FEE_FEATURE_BIT) <> 0 then
                Some <| ReadAmount stream
            else
                None

        let pegin =
            if int(features &&& KernelFeatures.PEGIN_FEATURE_BIT) <> 0 then
                Some <| ReadAmount stream
            else
                None

        let pegouts =
            if int(features &&& KernelFeatures.PEGOUT_FEATURE_BIT) <> 0 then
                ReadArray stream PegOutCoin.Read
            else
                Array.empty

        let lockHeight =
            if int(features &&& KernelFeatures.HEIGHT_LOCK_FEATURE_BIT) <> 0 then
                Some <| stream.ReadWrite Unchecked.defaultof<int>
            else
                None

        let stealthExcess =
            if int(features &&& KernelFeatures.STEALTH_EXCESS_FEATURE_BIT) <> 0 then
                Some <| PublicKey.Read stream
            else
                None
        
        let extraData =
            if int(features &&& KernelFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                ReadByteArray stream
            else
                Array.empty

        let excess = PedersenCommitment.Read stream
        let signature = Signature.Read stream

        {
            Features = features
            Fee = fee
            Pegin = pegin
            Pegouts = pegouts
            LockHeight = lockHeight
            StealthExcess = stealthExcess
            ExtraData = extraData
            Excess = excess
            Signature = signature
        }

    member self.GetSupplyChange() : Amount =
        let pegOutAmount = self.Pegouts |> Array.sumBy (fun pegOut -> pegOut.Amount)
        (self.Pegin |> Option.defaultValue 0L) - (self.Fee |> Option.defaultValue 0L) - pegOutAmount

    interface ISerializeable with
        member self.Write(stream) = 
            BetterAssert stream.Serializing "stream.Serializing should be true when writing"
            
            stream.ReadWrite (self.Features |> byte) |> ignore

            if int(self.Features &&& KernelFeatures.FEE_FEATURE_BIT) <> 0 then
                WriteAmount stream self.Fee.Value

            if int(self.Features &&& KernelFeatures.PEGIN_FEATURE_BIT) <> 0 then
                WriteAmount stream self.Pegin.Value

            if int(self.Features &&& KernelFeatures.PEGOUT_FEATURE_BIT) <> 0 then
                WriteArray stream self.Pegouts
            
            if int(self.Features &&& KernelFeatures.HEIGHT_LOCK_FEATURE_BIT) <> 0 then
                stream.ReadWrite self.LockHeight.Value |> ignore

            if int(self.Features &&& KernelFeatures.STEALTH_EXCESS_FEATURE_BIT) <> 0 then
                (self.StealthExcess.Value :> ISerializeable).Write stream

            if int(self.Features &&& KernelFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                WriteByteArray stream self.ExtraData

            (self.Excess :> ISerializeable).Write stream
            (self.Signature :> ISerializeable).Write stream

    interface IComparable<Kernel> with
        member self.CompareTo(other) =
            compare (Hasher.CalculateHash self) (Hasher.CalculateHash other)

    interface IComparable with
        member self.CompareTo(other) =
            match other with
            | :? Kernel as kernel -> (self :> IComparable<Kernel>).CompareTo kernel
            | _ -> 0

/// TRANSACTION BODY - Container for all inputs, outputs, and kernels in a transaction or block.
type TxBody =
    {
        /// List of inputs spent by the transaction.
        Inputs: array<Input>
        /// List of outputs the transaction produces.
        Outputs: array<Output>
        /// List of kernels that make up this transaction.
        Kernels: array<Kernel>
    }
    static member Read(stream: BitcoinStream) : TxBody =
        {
            Inputs = ReadArray stream Input.Read
            Outputs = ReadArray stream Output.Read
            Kernels = ReadArray stream Kernel.Read
        }

    interface ISerializeable with
        member self.Write stream = 
            WriteArray stream self.Inputs
            WriteArray stream self.Outputs
            WriteArray stream self.Kernels

type Transaction =
    {
        // The kernel "offset" k2 excess is k1G after splitting the key k = k1 + k2.
        KernelOffset: BlindingFactor
        StealthOffset: BlindingFactor
        // The transaction body.
        Body: TxBody
    }

    /// Parse hex-encoded MimbleWimble transaction
    static member ParseString(txString: string) : Transaction =
        let encoder = NBitcoin.DataEncoders.HexEncoder()
        let binaryTx = encoder.DecodeData txString
        use memoryStream = new MemoryStream(binaryTx)
        let bitcoinStream = new BitcoinStream(memoryStream, false)
        let result = Transaction.Read bitcoinStream
        result

    static member Read(stream: BitcoinStream) : Transaction =
        {
            KernelOffset = BlindingFactor.Read stream
            StealthOffset = BlindingFactor.Read stream
            Body = TxBody.Read stream
        }

    interface ISerializeable with
        member self.Write(stream) = 
            self.KernelOffset |> Write stream
            self.StealthOffset |> Write stream
            self.Body |> Write stream

/// Represents an output owned by the wallet, and the keys necessary to spend it.
/// See https://github.com/litecoin-project/litecoin/blob/master/src/libmw/include/mw/models/wallet/Coin.h
type Coin = 
    {
        AddressIndex: uint32
        SpendKey: Option<uint256>
        Blind: Option<BlindingFactor>
        Amount: Amount
        OutputId: Hash
        SenderKey: Option<uint256>
        Address: Option<StealthAddress>
        SharedSecret: Option<uint256>
    }
    static member ChangeIndex = 0u
    static member PeginIndex = 1u
    static member CustomKey = UInt32.MaxValue - 1u
    static member UnknownIndex = UInt32.MaxValue

    member self.IsChange = self.AddressIndex = Coin.ChangeIndex
    member self.IsPegIn = self.AddressIndex = Coin.PeginIndex
    member self.IsMine = self.AddressIndex <> Coin.UnknownIndex
    member self.HasSpendKey = self.SpendKey.IsSome

    static member Empty =
        {
            AddressIndex = Coin.UnknownIndex
            SpendKey = None
            Blind = None
            Amount = 0L
            OutputId = Hash(uint256 0UL)
            SenderKey = None
            Address = None
            SharedSecret = None
        }

type Recipient =
    {
        Amount: Amount
        Address: StealthAddress
    }
