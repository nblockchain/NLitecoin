﻿namespace NLitecoin

open System
open System.Reflection

open NBitcoin
open NBitcoin.DataEncoders


// internal to NBitcoin, so porting it here
type internal Witness(inputs: TxInList) =
    member self.IsNull() =
        inputs |> Seq.forall (fun i -> i.WitScript.PushCount = 0)

    member self.ReadWrite(stream: BitcoinStream) =
        for input in inputs do
            if stream.Serializing then
                let bytes = 
                    let script = 
                        match input.WitScript with
                        | null -> WitScript.Empty
                        | witScript -> witScript
                    script.ToBytes()
                stream.ReadWrite bytes
            else
                input.WitScript <- WitScript.Load stream

        if self.IsNull() then
            raise <| FormatException "Superfluous witness record"

[<AutoOpen>]
module private TxListExtensions =
    type TxOutList with
        member self.WithTransaction(transaction: Transaction) : TxOutList = 
            let result = TxOutList transaction
            if self.Count > 0 then
                result.AddRange self
            result

    type TxInList with
        member self.WithTransaction(transaction: Transaction) : TxInList = 
            let result = TxInList transaction
            if self.Count > 0 then
                result.AddRange self
            result

// supress obsolete warnings just like in https://github.com/MetacoSA/NBitcoin/blob/93ef4532b9f2ea52b2c910266eeb6684f3bd25de/NBitcoin.Altcoins/Litecoin.cs#L110
#nowarn "44"

type LitecoinTransaction() = 
    inherit Transaction()

    static let mwebExtensionTxFlag = 8uy

    member val MimbleWimbleTransaction: Option<MimbleWimble.Transaction> = None with get, set

    override self.GetConsensusFactory() = LitecoinConsensusFactory.Instance
    
    member private self.Read (stream: BitcoinStream) (witSupported: bool) =
        let mutable flags = 0uy
        self.nVersion <- stream.ReadWrite self.nVersion
        // Try to read the vin. In case the dummy is there, this will be read as an empty vector.
        stream.ReadWrite(&self.vin)
        self.vin <- self.vin.WithTransaction self
        let hasNoDummy = (self.nVersion &&& Transaction.NoDummyInput) <> 0u && self.vin.Count = 0
        if witSupported && hasNoDummy then
            self.nVersion <- self.nVersion &&& ~~~Transaction.NoDummyInput

        if self.vin.Count = 0 && witSupported && not hasNoDummy then
            // We read a dummy or an empty vin.
            flags <- stream.ReadWrite flags
            if flags <> 0uy then
                // Assume we read a dummy and a flag.
                stream.ReadWrite(&self.vin)
                self.vin <- self.vin.WithTransaction self
                stream.ReadWrite(&self.vout)
                self.vout <- self.vout.WithTransaction self
            else
                // Assume read a transaction without output.
                self.vout <- TxOutList self
        else
            // We read a non-empty vin. Assume a normal vout follows.
            stream.ReadWrite(&self.vout)
            self.vout <- self.vout.WithTransaction self
            
        if ((flags &&& 1uy) <> 0uy) && witSupported then
            // The witness flag is present, and we support witnesses.
            let wit = Witness self.Inputs
            wit.ReadWrite stream
            flags <- flags ^^^ 1uy
        
        if (flags &&& mwebExtensionTxFlag) <> 0uy then
            let version = ref 0uy
            stream.ReadWrite version
            self.MimbleWimbleTransaction <- Some(MimbleWimble.Transaction.Read stream)
            flags <- flags ^^^ 8uy

        if flags <> 0uy then
            // Unknown flag in the serialization
            raise <| FormatException "Unknown transaction optional data"

    member private self.Write (stream: BitcoinStream) (witSupported: bool) =
        let version = 
            if witSupported && (self.vin.Count = 0 && self.vout.Count > 0) then 
                self.nVersion ||| Transaction.NoDummyInput 
            else 
                self.nVersion
        stream.ReadWrite version |> ignore

        let flags =
            if witSupported then
                // Check whether witnesses need to be serialized.
                if self.HasWitness then
                    1uy
                else
                    0uy
            else
                0uy

        let flags = 
            if self.MimbleWimbleTransaction.IsSome then 
                flags ||| mwebExtensionTxFlag 
            else 
                flags 

        let flags = 
            if flags <> 0uy then
                // Use extended format in case witnesses are to be serialized.
                let vinDummy = TxInList()
                stream.ReadWrite(ref vinDummy)
                stream.ReadWrite flags
            else
                flags

        stream.ReadWrite(&self.vin)
        self.vin <- self.vin.WithTransaction self
        stream.ReadWrite(&self.vout)
        self.vout <- self.vout.WithTransaction self
        if (flags &&& 1uy) <> 0uy then
            let wit = Witness self.Inputs
            wit.ReadWrite stream

        match self.MimbleWimbleTransaction with
        | Some mwebTransaction -> 
            stream.ReadWrite MimbleWimble.Transaction.Version |> ignore
            (mwebTransaction :> MimbleWimble.ISerializeable).Write stream
        | None -> ()

    override self.ReadWrite(stream: BitcoinStream) =
        let witSupported = 
            (((uint32 stream.TransactionOptions) &&& (uint32 TransactionOptions.Witness)) <> 0u) &&
            stream.ProtocolCapabilities.SupportWitness

        if not stream.Serializing then
            self.Read stream witSupported
        else
            self.Write stream witSupported
        
        stream.ReadWriteStruct(&self.nLockTime)

and LitecoinBlockHeader() =
    inherit BlockHeader()
        
    override self.GetPoWHash() : uint256 =
        let headerBytes = self.ToBytes()
        let hash = NBitcoin.Crypto.SCrypt.ComputeDerivedKey(headerBytes, headerBytes, 1024, 1, 1, Nullable(), 32)
        uint256 hash

and LitecoinBlock(header: LitecoinBlockHeader) = 
    inherit Block(header)

    override self.GetConsensusFactory() : ConsensusFactory =
        LitecoinConsensusFactory.Instance

and LitecoinMainnetAddressStringParser() =
    inherit NetworkStringParser()

    override self.TryParse(str: string, network: Network, targetType: Type, result: byref<IBitcoinString>) =
        let successLptv = 
            if str.StartsWith("Ltpv", StringComparison.OrdinalIgnoreCase) && targetType.GetTypeInfo().IsAssignableFrom(typeof<BitcoinExtKey>.GetTypeInfo()) then
                try
                    let decoded = 
                        Array.append
                            [|  0x04uy; 0x88uy; 0xADuy; 0xE4uy |]
                            (Encoders.Base58Check.DecodeData str |> Array.skip 4)
                    result <- BitcoinExtKey(Encoders.Base58Check.EncodeData decoded, network)
                    true
                with
                | _ -> 
                    false
            else
                false
        
        if successLptv then
            true
        else
            let successLtub =
                if str.StartsWith("Ltub", StringComparison.OrdinalIgnoreCase) && targetType.GetTypeInfo().IsAssignableFrom(typeof<BitcoinExtPubKey>.GetTypeInfo()) then
                    try
                        let decoded = 
                            Array.append
                                [| 0x04uy; 0x88uy; 0xB2uy; 0x1Euy |]
                                (Encoders.Base58Check.DecodeData str |> Array.skip 4)
                        result <- BitcoinExtPubKey(Encoders.Base58Check.EncodeData decoded, network)
                        true
                    with
                    | _ -> 
                        false
                else
                    false
            if successLtub then
                true
            else
                base.TryParse(str, network, targetType, &result)

and LitecoinConsensusFactory private() =
    inherit ConsensusFactory()

    static member val Instance = new LitecoinConsensusFactory()

    override self.CreateTransaction() = LitecoinTransaction()
    override self.CreateBlockHeader() = LitecoinBlockHeader()
    override self.CreateBlock() = LitecoinBlock(LitecoinBlockHeader())

type Litecoin private() =
    inherit NetworkSetBase()

    static let pnSeed6_main : array<array<byte> * int> =
        [|
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x01uy; 0xcauy; 0x80uy; 0xdauy |], 10333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x18uy; 0x92uy; 0x06uy; 0x11uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x1fuy; 0x1fuy; 0x4fuy; 0x86uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x25uy; 0x3buy; 0x18uy; 0x0fuy |], 8331
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x25uy; 0x61uy; 0xa8uy; 0xc8uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x25uy; 0x8buy; 0x09uy; 0xf8uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x26uy; 0x6duy; 0xdauy; 0x72uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2duy; 0x28uy; 0x89uy; 0x72uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2duy; 0x37uy; 0xb0uy; 0x1auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2euy; 0x1cuy; 0xc9uy; 0x44uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2euy; 0x94uy; 0x10uy; 0xcauy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2euy; 0xacuy; 0x04uy; 0x1fuy |], 9335
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2euy; 0xf9uy; 0x2fuy; 0xe9uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2fuy; 0x5auy; 0x04uy; 0x29uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2fuy; 0x5auy; 0x2euy; 0xcbuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x2fuy; 0xbduy; 0x81uy; 0xdauy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x32uy; 0x07uy; 0x2fuy; 0x5auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x32uy; 0x16uy; 0x67uy; 0x82uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x34uy; 0x29uy; 0x09uy; 0x40uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x3cuy; 0xcduy; 0x3auy; 0x20uy |], 7749
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x3fuy; 0xe7uy; 0xefuy; 0xd4uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x49uy; 0x59uy; 0xc3uy; 0x81uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x4auy; 0xd0uy; 0x2buy; 0x36uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x50uy; 0xdeuy; 0x27uy; 0x4duy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x50uy; 0xf1uy; 0xdauy; 0x38uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x52uy; 0xa5uy; 0x80uy; 0xd5uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x53uy; 0x95uy; 0x7duy; 0x4fuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x53uy; 0xacuy; 0x45uy; 0x9auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x53uy; 0xd4uy; 0x75uy; 0x8cuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x54uy; 0x34uy; 0x91uy; 0x24uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x54uy; 0x57uy; 0x79uy; 0x0buy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x54uy; 0x92uy; 0x3fuy; 0xdfuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x55uy; 0x19uy; 0x92uy; 0x4auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x58uy; 0xb9uy; 0x9buy; 0x86uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x5buy; 0xe2uy; 0x0auy; 0x5auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x5buy; 0xf0uy; 0x8duy; 0xafuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x5euy; 0x71uy; 0x9cuy; 0xdduy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x60uy; 0x38uy; 0x91uy; 0xfauy |], 10333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x60uy; 0xffuy; 0x06uy; 0xfduy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x68uy; 0xdfuy; 0x3buy; 0x8cuy |], 23333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x6cuy; 0x1fuy; 0x0fuy; 0x9auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x6duy; 0xecuy; 0x5auy; 0x7auy |], 59333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x6fuy; 0xcduy; 0x01uy; 0xf6uy |], 10333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x71uy; 0x0auy; 0x9cuy; 0xb6uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x72uy; 0x37uy; 0x4auy; 0x02uy |], 20044
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x74uy; 0x7duy; 0x78uy; 0x1auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x77uy; 0x3fuy; 0x2cuy; 0x85uy |], 19992
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x77uy; 0x93uy; 0x89uy; 0x9buy |], 19992
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x86uy; 0xd5uy; 0xdeuy; 0xa1uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x93uy; 0x9cuy; 0x54uy; 0xbauy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0x95uy; 0xd2uy; 0xabuy; 0xe1uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xa2uy; 0xf3uy; 0xd8uy; 0xf4uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xa3uy; 0xacuy; 0x21uy; 0x4euy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xa3uy; 0xacuy; 0x23uy; 0xf7uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xaduy; 0xd0uy; 0xc2uy; 0x5euy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xaeuy; 0x3cuy; 0x89uy; 0x4cuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xb2uy; 0x3fuy; 0x12uy; 0x03uy |], 9335
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xb2uy; 0x3fuy; 0x72uy; 0x19uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xb2uy; 0xfeuy; 0x28uy; 0x29uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xb7uy; 0x3duy; 0x92uy; 0x85uy |], 19992
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xb9uy; 0x3cuy; 0xf4uy; 0xfbuy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xb9uy; 0x57uy; 0xb8uy; 0x1duy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xbcuy; 0x00uy; 0xb6uy; 0x0auy |], 9335
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xbcuy; 0x8auy; 0x21uy; 0x21uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xbcuy; 0x9buy; 0x88uy; 0x46uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xc0uy; 0x63uy; 0x3euy; 0x17uy |], 5001
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xc0uy; 0xc6uy; 0x64uy; 0x54uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xc0uy; 0xf1uy; 0xa6uy; 0x70uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xc6uy; 0x0cuy; 0x4buy; 0x19uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xcbuy; 0xb1uy; 0x8euy; 0x25uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xd3uy; 0x6euy; 0x01uy; 0x11uy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xd3uy; 0x95uy; 0xf6uy; 0x96uy |], 1022
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xd4uy; 0x5duy; 0xe2uy; 0x5auy |], 9333
            [| 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0xffuy; 0xffuy; 0xd5uy; 0x7euy; 0x8duy; 0x3cuy |], 9333
        |]
    
    static member val Instance = Litecoin()

    override self.CryptoCode = "LTC"

    override self.CreateMainnet() : NetworkBuilder =
        let bech32 = Encoders.Bech32 "ltc"
        let builder = NetworkBuilder()
        builder
            .SetConsensus(
                Consensus(
                    SubsidyHalvingInterval = 840000,
                    MajorityEnforceBlockUpgrade = 750,
                    MajorityRejectBlockOutdated = 950,
                    MajorityWindow = 1000,
                    BIP34Hash = uint256 "fa09d204a83a768ed5a7c8d441fa62f2043abf420cff1226c7b4329aeb9d51cf",
                    PowLimit = Target(uint256 "00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
                    PowTargetTimespan = TimeSpan.FromSeconds(3.5 * 24.0 * 60.0 * 60.0),
                    PowTargetSpacing = TimeSpan.FromSeconds(2.5 * 60.0),
                    PowAllowMinDifficultyBlocks = false,
                    PowNoRetargeting = false,
                    RuleChangeActivationThreshold = 6048,
                    MinerConfirmationWindow = 8064,
                    CoinbaseMaturity = 100,
                    LitecoinWorkCalculation = true,
                    ConsensusFactory = LitecoinConsensusFactory.Instance,
                    SupportSegwit = true,
                    SupportTaproot = true
                )
            )
            .SetBase58Bytes(Base58Type.PUBKEY_ADDRESS, [| 48uy |])
            .SetBase58Bytes(Base58Type.SCRIPT_ADDRESS, [| 50uy |])
            .SetBase58Bytes(Base58Type.SECRET_KEY, [| 176uy |])
            .SetBase58Bytes(Base58Type.EXT_PUBLIC_KEY, [| 0x04uy; 0x88uy; 0xB2uy; 0x1Euy |])
            .SetBase58Bytes(Base58Type.EXT_SECRET_KEY, [| 0x04uy; 0x88uy; 0xADuy; 0xE4uy |])
            .SetNetworkStringParser(LitecoinMainnetAddressStringParser())
            .SetBech32(Bech32Type.WITNESS_PUBKEY_ADDRESS, bech32)
            .SetBech32(Bech32Type.WITNESS_SCRIPT_ADDRESS, bech32)
            .SetBech32(Bech32Type.TAPROOT_ADDRESS, bech32)
            .SetMagic(0xdbb6c0fbu)
            .SetPort(9333)
            .SetRPCPort(9332)
            .SetName("ltc-main")
            .AddAlias("ltc-mainnet")
            .AddAlias("litecoin-mainnet")
            .AddAlias("litecoin-main")
            .SetUriScheme("litecoin")
            .AddSeeds(NetworkSetBase.ToSeed pnSeed6_main)
            .SetGenesis("010000000000000000000000000000000000000000000000000000000000000000000000d9ced4ed1130f7b7faad9be25323ffafa33232a17c3edf6cfd97bee6bafbdd97b9aa8e4ef0ff0f1ecd513f7c0101000000010000000000000000000000000000000000000000000000000000000000000000ffffffff4804ffff001d0104404e592054696d65732030352f4f63742f32303131205374657665204a6f62732c204170706c65e280997320566973696f6e6172792c2044696573206174203536ffffffff0100f2052a010000004341040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9ac00000000")
    
    /// not used in GWallet
    override self.CreateTestnet() =
        null

    /// not used in GWallet
    override self.CreateRegtest() =
        null
