module NLitecoin.MimbleWimble.SerializationTests

open System.IO

open NUnit.Framework
open FsCheck
open FsCheck.NUnit
open NBitcoin

open NLitecoin.MimbleWimble


let roundtripObject<'T when 'T :> ISerializeable and 'T : equality> (object: 'T) (readFunc: BitcoinStream -> 'T) =
    use memoryStream = new MemoryStream()
    let writeStream = new BitcoinStream(memoryStream, true)
    object.Write writeStream
    memoryStream.Flush()
    memoryStream.Position <- 0
    let readStream = new BitcoinStream(memoryStream, false)
    let deserialized = readFunc readStream
    deserialized = object


type Generators =
    static member BigintGenerator (numBytes: int) = 
        gen {
            let! bytes = Gen.listOfLength numBytes (Gen.choose(0, 255) |> Gen.map byte)
            return bytes |> List.toArray |> BigInt
        }

    static member uint256() =
        { new Arbitrary<uint256>() with
            override _.Generator =
                Gen.listOfLength 32 (Gen.choose(0, 255) |> Gen.map byte)
                |> Gen.map (List.toArray >> uint256) }
    
    static member PedersenCommitment() =
        { new Arbitrary<PedersenCommitment>() with
            override _.Generator =
                Generators.BigintGenerator PedersenCommitment.NumBytes
                |> Gen.map PedersenCommitment }

    static member Signature() =
        { new Arbitrary<Signature>() with
            override _.Generator =
                Generators.BigintGenerator Signature.NumBytes
                |> Gen.map Signature }

    static member PublicKey() =
        { new Arbitrary<PublicKey>() with
            override _.Generator =
                Generators.BigintGenerator PublicKey.NumBytes
                |> Gen.map PublicKey }

    static member Input() =
        { new Arbitrary<Input>() with
            override _.Generator =
                gen {
                    let! features = 
                        Gen.elements 
                            [ 
                                InputFeatures.EXTRA_DATA_FEATURE_BIT
                                InputFeatures.STEALTH_KEY_FEATURE_BIT
                                InputFeatures.EXTRA_DATA_FEATURE_BIT ||| InputFeatures.STEALTH_KEY_FEATURE_BIT
                            ]
                    let! outputId = Arb.generate<Hash>
                    let! commitment = Arb.generate<PedersenCommitment>
                    let! outputPubKey = Arb.generate<PublicKey>
                    let! signature = Arb.generate<Signature>
                    let! inputPubKeyValue = Arb.generate<PublicKey>
                    let inputPubKey = 
                        if int(features &&& InputFeatures.STEALTH_KEY_FEATURE_BIT) <> 0 then
                            Some inputPubKeyValue
                        else
                            None
                    let! extraData = 
                        let len = 
                            if int(features &&& InputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                                100
                            else
                                0
                        Gen.listOfLength len Arb.generate<byte>
                        |> Gen.map List.toArray
                    return {
                        Features = features
                        OutputID = outputId
                        Commitment = commitment
                        InputPublicKey = inputPubKey
                        OutputPublicKey = outputPubKey
                        ExtraData = extraData
                        Signature = signature
                    }
                } }

    static member OutputMessage() =
        { new Arbitrary<OutputMessage>() with
            override _.Generator =
                gen {
                    let! features = 
                        Gen.elements 
                            [ 
                                OutputFeatures.EXTRA_DATA_FEATURE_BIT
                                OutputFeatures.STANDARD_FIELDS_FEATURE_BIT
                                OutputFeatures.EXTRA_DATA_FEATURE_BIT ||| OutputFeatures.STANDARD_FIELDS_FEATURE_BIT
                            ]
                    let! standardFieldsValue = Arb.generate<OutputMessageStandardFields>
                    let! maskedNonce = Generators.BigintGenerator OutputMessageStandardFields.MaskedNonceNumBytes
                    let standardFields =
                        if int(features &&& OutputFeatures.STANDARD_FIELDS_FEATURE_BIT) <> 0 then
                            Some { standardFieldsValue with MaskedNonce = maskedNonce }
                        else
                            None
                    let! extraData = 
                        let len = 
                            if int(features &&& OutputFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                                100
                            else
                                0
                        Gen.listOfLength len Arb.generate<byte>
                        |> Gen.map List.toArray
                    return {
                        Features = features
                        StandardFields = standardFields
                        ExtraData = extraData
                    }
                } }

    static member RangeProof() =
        { new Arbitrary<RangeProof>() with
            override _.Generator =
                gen {
                    let! data = Gen.listOfLength RangeProof.Size Arb.generate<byte>
                    return RangeProof(data |> List.toArray)
                } }

    static member PegOutCoin() =
        { new Arbitrary<PegOutCoin>() with
            override _.Generator =
                gen {
                    let! camount = Arb.generate<Amount>
                    return {
                        Amount = camount
                        ScriptPubKey = NBitcoin.Script.Empty
                    }
                } }

    static member Kernel() =
        { new Arbitrary<Kernel>() with
            override _.Generator =
                gen {
                    let! fetauresList = Gen.subListOf (KernelFeatures.GetValues<KernelFeatures>())
                    let features = fetauresList |> List.fold (fun a b -> a ||| b) (enum<KernelFeatures> 0)
                    let! fee =
                        if int(features &&& KernelFeatures.FEE_FEATURE_BIT) <> 0 then
                            Arb.generate<Amount> |> Gen.map Some
                        else
                            Gen.constant None
                    let! pegin =
                        if int(features &&& KernelFeatures.PEGIN_FEATURE_BIT) <> 0 then
                            Arb.generate<Amount> |> Gen.map Some
                        else
                            Gen.constant None
                    let! pegouts =
                        if int(features &&& KernelFeatures.PEGOUT_FEATURE_BIT) <> 0 then
                            Arb.generate<PegOutCoin> |> Gen.nonEmptyListOf
                        else
                            Gen.constant List.empty
                    let! lockHeight =
                        if int(features &&& KernelFeatures.HEIGHT_LOCK_FEATURE_BIT) <> 0 then
                            Arb.generate<int> |> Gen.map Some
                        else
                            Gen.constant None
                    let! stealthExcess =
                        if int(features &&& KernelFeatures.STEALTH_EXCESS_FEATURE_BIT) <> 0 then
                            Arb.generate<PublicKey> |> Gen.map Some
                        else
                            Gen.constant None
                    let! extraData =
                        if int(features &&& KernelFeatures.EXTRA_DATA_FEATURE_BIT) <> 0 then
                            Arb.generate<byte> |> Gen.nonEmptyListOf
                        else
                            Gen.constant List.empty
                    let! excess = Arb.generate<PedersenCommitment>
                    let! signature = Arb.generate<Signature>
                    return {
                        Features = features
                        Fee = fee
                        Pegin = pegin
                        Pegouts = pegouts |> List.toArray
                        LockHeight = lockHeight
                        StealthExcess = stealthExcess
                        ExtraData = extraData |> List.toArray
                        Excess = excess
                        Signature = signature
                    }
                } }

[<Property(Arbitrary=[|typeof<Generators>|])>]
let Uint256Roundtrip(number: uint256) =
    use memoryStream = new MemoryStream()
    let writeStream = new BitcoinStream(memoryStream, true)
    Helpers.WriteUint256 writeStream number
    memoryStream.Flush()
    memoryStream.Position <- 0
    let readStream = new BitcoinStream(memoryStream, false)
    Helpers.ReadUint256 readStream = number

[<Property(Arbitrary=[|typeof<Generators>|])>]
let PedersenCommitmentRoundtrip(commitment: PedersenCommitment) =
    roundtripObject commitment PedersenCommitment.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let PublicKeyRoundtrip(pubKey: PublicKey) =
    roundtripObject pubKey PublicKey.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let SignatureRoundtrip(signature: Signature) =
    roundtripObject signature Signature.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let InputRoundtrip(input: Input) =
    roundtripObject input Input.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let OutputMessageRoundtrip(input: OutputMessage) =
    roundtripObject input OutputMessage.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let OutputRoundtrip(output: Output) =
    roundtripObject output Output.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let PegOutCoinRoundtrip(pegoutCoin: PegOutCoin) =
    roundtripObject pegoutCoin PegOutCoin.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let KernelRoundtrip(kernel: Kernel) =
    roundtripObject kernel Kernel.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let TxBodyRoundtrip(txBody: TxBody) =
    roundtripObject txBody TxBody.Read

[<Property(Arbitrary=[|typeof<Generators>|])>]
let TransactionRoundtrip(transaction: Transaction) =
    roundtripObject transaction Transaction.Read

/// Deserialize transaction generated and serialized by modified litecoin test 
/// (see https://github.com/litecoin-project/litecoin/blob/5ac781487cc9589131437b23c69829f04002b97e/src/libmw/test/tests/models/tx/Test_Transaction.cpp)
[<Test>]
let TestTransactionDeserilaization() =
    let serializedTransaction = File.ReadAllBytes "transaction.bin"
    let bitcoinStream = BitcoinStream serializedTransaction
    let transaction = Transaction.Read bitcoinStream

    Assert.AreEqual(transaction.Body.Kernels[0].Pegin, Some 123L)
    Assert.AreEqual(transaction.Body.Kernels[1].Fee, Some 5L)

[<Property(Arbitrary=[|typeof<Generators>|])>]
let StealthAddressStringEncodingRoundtrip(stealthAddress: StealthAddress) =
    let encoded = stealthAddress.EncodeDestination()
    StealthAddress.DecodeDestination encoded = stealthAddress
