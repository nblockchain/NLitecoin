﻿namespace NLitecoin.MimbleWimble

open System
open System.IO

open NBitcoin
open NBitcoin.Protocol
open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Parameters

type ISerializeable =
    abstract Write: BitcoinStream -> unit
    // no Read() method as it will be static method and can't be included in interface

type CAmount = int64

[<AutoOpen>]
module Helpers =
    let write (stream: BitcoinStream) (object: #ISerializeable) =
        assert(stream.Serializing)
        object.Write stream

    let writeUint256 (stream: BitcoinStream) (number: uint256) =
        assert(stream.Serializing)
        number.AsBitcoinSerializable().ReadWrite stream

    let readUint256 (stream: BitcoinStream) : uint256 =
        assert(not stream.Serializing)
        let tempValue = uint256.MutableUint256()
        tempValue.ReadWrite stream
        tempValue.Value
    
    let readArray<'T> (stream: BitcoinStream) (readFunc : BitcoinStream -> 'T) : array<'T> =
        let len = int <| VarInt.StaticRead stream
        Array.init len (fun _ -> readFunc stream)

    let writeArray<'T when 'T :> ISerializeable> (stream: BitcoinStream) (arr: array<'T>) =
        let len = uint64 arr.Length
        VarInt.StaticWrite(stream, len)
        for each in arr do
            each.Write stream

    let readCAmount (stream: BitcoinStream) : CAmount =
        let amountRef = ref 0L
        stream.ReadWrite amountRef
        amountRef.Value

type BlindingFactor = 
    | BlindindgFactor of uint256
    static member Read(stream: BitcoinStream) : BlindingFactor =
        BlindindgFactor(readUint256 stream)

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | BlindindgFactor number -> number |> writeUint256 stream

type Hash = 
    | Hash of uint256
    static member Read(stream: BitcoinStream) : Hash =
        readUint256 stream |> Hash

    interface ISerializeable with
        member self.Write(stream) =
            match self with
            | Hash number -> number |> writeUint256 stream

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

    static member Read(stream: BitcoinStream) (numBytes: int) : BigInt =
        assert(not stream.Serializing)
        let result : ref<array<uint8>> = Array.zeroCreate numBytes |> ref
        stream.ReadWrite result
        BigInt result.Value

    interface ISerializeable with
        member self.Write(stream) =
            assert(stream.Serializing)
            stream.ReadWrite (self.Data |> ref)

type PedersenCommitment = 
    | PedersenCommitment of BigInt
    static member NumBytes = 33

    static member Read(stream: BitcoinStream) =
        PedersenCommitment(BigInt.Read stream PedersenCommitment.NumBytes)

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
        assert(not stream.Serializing)
        let featuresByte = ref 0uy
        stream.ReadWrite featuresByte
        let features = featuresByte.Value |> int |> enum<InputFeatures>
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
                let bytes = ref Array.empty<byte>
                stream.ReadWrite bytes
                bytes.Value
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
        member self.Write(stream) = raise <| System.NotImplementedException()

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
        assert(not stream.Serializing)

        let featuresByte = ref 0uy
        stream.ReadWrite featuresByte
        let features = featuresByte.Value |> int |> enum<OutputFeatures>
        
        let standardFields =
            if int(features &&& OutputFeatures.STANDARD_FIELDS_FEATURE_BIT) <> 0 then
                let pubKey = PublicKey.Read stream
                let viewTag = ref 0uy
                stream.ReadWrite viewTag
                let maskedValue = ref 0UL
                stream.ReadWrite maskedValue
                let maskedNonce = BigInt.Read stream OutputMessageStandardFields.MaskedNonceNumBytes
                {
                    KeyExchangePubkey = pubKey
                    ViewTag = viewTag.Value
                    MaskedValue = maskedValue.Value
                    MaskedNonce = maskedNonce
                }
                |> Some
            else
                None

        let extraData =
            if int(features &&& OutputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                let data = ref Array.empty<uint8>
                stream.ReadWrite data
                data.Value
            else
                Array.empty

        let result = 
            {
                Features = features
                StandardFields = standardFields
                ExtraData = extraData
            }

        result

    interface ISerializeable with
        member self.Write(stream) = 
            assert(stream.Serializing)
            
            stream.ReadWrite(self.Features |> uint8) |> ignore

            if int(self.Features &&& OutputFeatures.STANDARD_FIELDS_FEATURE_BIT) <> 0 then
                let fields = self.StandardFields.Value
                write stream fields.KeyExchangePubkey
                stream.ReadWrite fields.ViewTag |> ignore
                stream.ReadWrite fields.MaskedValue |> ignore
                (fields.MaskedNonce :> ISerializeable).Write stream

            if int(self.Features &&& OutputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                stream.ReadWrite(ref self.ExtraData)

type RangeProof(bytes: array<uint8>) =
    do assert(bytes.Length <= 675)

    member _.Data = bytes

    static member Read(stream: BitcoinStream) : RangeProof =
        assert(not stream.Serializing)
        let result = ref Array.empty<uint8>
        stream.ReadWrite result
        RangeProof result.Value

    interface ISerializeable with
        member self.Write(stream) = 
            assert(not stream.Serializing)
            stream.ReadWrite(ref bytes)

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
        assert(not stream.Serializing)
        {
            Commitment = PedersenCommitment.Read stream
            SenderPublicKey = PublicKey.Read stream
            ReceiverPublicKey = PublicKey.Read stream
            Message = OutputMessage.Read stream
            RangeProof = RangeProof.Read stream
            Signature = Signature.Read stream
        }

    interface ISerializeable with
        member self.Write(stream) = raise <| System.NotImplementedException()

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
        Amount: CAmount
        ScriptPubKey: NBitcoin.Script // ?
    }
    static member Read(stream: BitcoinStream) : PegOutCoin =
        assert(not stream.Serializing)
        let amount = readCAmount stream
        let scriptPubKeyRef = ref NBitcoin.Script.Empty
        stream.ReadWrite scriptPubKeyRef
        {
            Amount = amount
            ScriptPubKey = scriptPubKeyRef.Value
        }

    interface ISerializeable with
        member self.Write(stream) = raise <| System.NotImplementedException()

type Kernel =
    {
        Features: KernelFeatures
        Fee: Option<CAmount>
        Pegin: Option<CAmount>
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
        assert(not stream.Serializing)
        let featuresRef = ref 0uy
        stream.ReadWrite featuresRef
        let features = featuresRef.Value |> int |> enum<KernelFeatures>

        let fee =
            if int(features &&& KernelFeatures.FEE_FEATURE_BIT) <> 0 then
                Some <| readCAmount stream
            else
                None

        let pegin =
            if int(features &&& KernelFeatures.PEGIN_FEATURE_BIT) <> 0 then
                Some <| readCAmount stream
            else
                None

        let pegouts =
            if int(features &&& KernelFeatures.PEGOUT_FEATURE_BIT) <> 0 then
                readArray stream PegOutCoin.Read
            else
                Array.empty

        let lockHeight =
            if int(features &&& KernelFeatures.HEIGHT_LOCK_FEATURE_BIT) <> 0 then
                let valueRef = ref 0
                stream.ReadWrite valueRef
                Some valueRef.Value
            else
                None

        let stealthExcess =
            if int(features &&& KernelFeatures.STEALTH_EXCESS_FEATURE_BIT) <> 0 then
                Some <| PublicKey.Read stream
            else
                None
        
        let extraData =
            let bytesRef = ref Array.empty<byte>
            if int(features &&& KernelFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                stream.ReadWrite bytesRef
            bytesRef.Value

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

    interface ISerializeable with
        member self.Write(stream) = raise <| System.NotImplementedException()

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
            Inputs = readArray stream Input.Read
            Outputs = readArray stream Output.Read
            Kernels = readArray stream Kernel.Read
        }

    interface ISerializeable with
        member self.Write(stream) = 
            writeArray stream self.Inputs
            writeArray stream self.Outputs
            writeArray stream self.Kernels

type Transaction =
    {
        // The kernel "offset" k2 excess is k1G after splitting the key k = k1 + k2.
        KernelOffset: BlindingFactor
        StealthOffset: BlindingFactor
        // The transaction body.
        Body: TxBody
    }
    static member ParseString(txString: string) : Transaction =
        let encoder = NBitcoin.DataEncoders.HexEncoder()
        let binaryTx = encoder.DecodeData txString
        use memoryStream = new MemoryStream(binaryTx)
        let bitcoinStream = new BitcoinStream(memoryStream, false)
        Transaction.Read bitcoinStream

    static member Read(stream: BitcoinStream) : Transaction =
        let result =
            {
                KernelOffset = BlindingFactor.Read stream
                StealthOffset = BlindingFactor.Read stream
                Body = TxBody.Read stream
            }
        
        result

    interface ISerializeable with
        member self.Write(stream) = 
            self.KernelOffset |> write stream
            self.StealthOffset |> write stream
            self.Body |> write stream
