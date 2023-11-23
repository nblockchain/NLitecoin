module NLitecoin.MimbleWimble.Wallet

open System

open NBitcoin
open Org.BouncyCastle.Math

open EC

let KeyPurposeMweb = 100

type Coin = NLitecoin.MimbleWimble.Coin
type Transaction = NLitecoin.MimbleWimble.Transaction
type MutableDictionary<'K,'V> = Collections.Generic.Dictionary<'K,'V>

type IKeyChain =
    abstract GetStealthAddress: uint32 -> StealthAddress
    abstract RewindOutput: Output -> Option<Coin>
    abstract PrivateScanKey: Key

let RewindOutput 
    (keyChain: IKeyChain) 
    (getIndexForSpendKey: Secp256k1.ECPubKey -> Option<uint32>) 
    (calculateOutputKey: uint256 -> uint32 -> Option<uint256>)
    (output: Output) : Option<Coin> =
    match output.Message.StandardFields with
    | None -> None
    | Some outputFields ->
        let sharedSecret = 
            Secp256k1.ECPubKey.Create(outputFields.KeyExchangePubkey.ToBytes())
                .TweakMul(keyChain.PrivateScanKey.ToBytes())
                .ToBytes(true) 
                |> BigInt 
                |> PublicKey
        let viewTag = 
            let hasher = Hasher HashTags.TAG
            hasher.Append sharedSecret
            hasher.Hash().ToBytes().[0]
        if viewTag <> outputFields.ViewTag then
            None
        else
            /// t
            let ecdheSharedSecret = 
                let hasher = Hasher HashTags.DERIVE
                hasher.Append sharedSecret
                hasher.Hash()

            /// B_i
            let spendPubKey = 
                let tHashed =
                    let hasher = Hasher HashTags.OUT_KEY
                    hasher.Append ecdheSharedSecret
                    hasher.Hash().ToBytes() |> BigInteger.FromByteArrayUnsigned
                Secp256k1.ECPubKey.Create(output.ReceiverPublicKey.ToBytes())
                    .TweakMul((tHashed.ModInverse EC.scalarOrder).ToByteArrayUnsigned())
                
            match getIndexForSpendKey spendPubKey with
            | None -> None
            | Some index ->
                let mask = OutputMask.FromShared(ecdheSharedSecret.ToUInt256())
                let value = mask.MaskValue outputFields.MaskedValue |> int64
                /// n
                let maskNonce = mask.MaskNonce outputFields.MaskedNonce

                if Pedersen.Commit value (Pedersen.BlindSwitch mask.PreBlind value) <> output.Commitment then
                    None
                else
                    let address = 
                        { 
                            SpendPubKey = spendPubKey.ToBytes true |> BigInt |> PublicKey
                            ScanPubKey = 
                                spendPubKey.TweakMul(keyChain.PrivateScanKey.ToBytes())
                                    .ToBytes(true) 
                                    |> BigInt 
                                    |> PublicKey 
                        }
                    // sending key 's' and check that s*B ?= Ke
                    let sendKey = 
                        let hasher = Hasher HashTags.SEND_KEY
                        hasher.Append address.ScanPubKey
                        hasher.Append address.SpendPubKey
                        hasher.Write(BitConverter.GetBytes value)
                        hasher.Append maskNonce
                        hasher.Hash()
                    if outputFields.KeyExchangePubkey.ToBytes() <> 
                        spendPubKey.TweakMul(sendKey.ToBytes()).ToBytes(true) then
                        None
                    else
                        {
                            AddressIndex = index
                            Blind = Some mask.PreBlind
                            Amount = value
                            OutputId = output.GetOutputID()
                            Address = Some address
                            SharedSecret = Some(ecdheSharedSecret.ToUInt256())
                            SpendKey = calculateOutputKey (ecdheSharedSecret.ToUInt256()) index
                            SenderKey = None
                        }
                        |> Some

let GetStealthAddress (spendPubKey: Secp256k1.ECPubKey) (privateScanKey: Key) : StealthAddress =
    {
        SpendPubKey = spendPubKey.ToBytes(true) |> BigInt |> PublicKey
        ScanPubKey = spendPubKey.TweakMul(privateScanKey.ToBytes()).ToBytes(true) |> BigInt |> PublicKey
    }

type KeyChain(seed: array<byte>, maxUsedIndex: uint32) =
    let masterKey = ExtKey.CreateFromSeed seed
    // derive m/0'
    let accountKey = masterKey.Derive(0, true)
    // derive m/0'/100' (MWEB)
    let chainChildKey = accountKey.Derive(KeyPurposeMweb, true)

    let scanKey = chainChildKey.Derive(0, true)
    let spendKey = chainChildKey.Derive(1, true)

    let calculateSpendKey(index: uint32) : Secp256k1.ECPrivKey =
        let mi =
            let hasher = Hasher HashTags.ADDRESS
            hasher.Write(BitConverter.GetBytes index)
            hasher.Write(scanKey.PrivateKey.ToBytes())
            hasher.Hash()
        Secp256k1.ECPrivKey.Create(spendKey.PrivateKey.ToBytes()).TweakAdd(mi.ToBytes())

    // have to use dictionary as Secp256k1.ECPubKey doesn't implement comparison
    let spendPubKeysMap = 
        MutableDictionary<Secp256k1.ECPubKey, uint32>(
            seq { 
                for i in 0u..maxUsedIndex -> 
                    let spendPubKey = (calculateSpendKey i).CreatePubKey()
                    Collections.Generic.KeyValuePair(spendPubKey, i) })

    static member DefaultInitialMaxUsedIndex = 100u

    new(seed: array<byte>) = KeyChain(seed, KeyChain.DefaultInitialMaxUsedIndex)

    interface IKeyChain with
        override self.GetStealthAddress index = self.GetStealthAddress index
        override self.RewindOutput output = self.RewindOutput output
        override self.PrivateScanKey = self.ScanKey.PrivateKey

    member self.MaxUsedIndex : uint32 = spendPubKeysMap.Values |> Seq.max

    member self.ScanKey = scanKey
    member self.SpendKey = spendKey

    member self.GetIndexForSpendKey(key: Secp256k1.ECPubKey) : Option<uint32> =
       match spendPubKeysMap.TryGetValue key with
       | (true, value) -> Some value
       | _ -> None

    member self.GetStealthAddress(index: uint32) : StealthAddress =
        let spendPubKey = self.GetSpendKey(index)
        GetStealthAddress spendPubKey scanKey.PrivateKey
    
    member self.GetSpendKey(index: uint32) : Secp256k1.ECPubKey =
        match spendPubKeysMap |> Seq.tryFind (fun item -> item.Value = index) with
        | Some item -> item.Key
        | None ->
            let spendKey = (calculateSpendKey index).CreatePubKey()
            spendPubKeysMap.[spendKey] <- index
            spendKey

    member self.RewindOutput(output: Output) : Option<Coin> =
        RewindOutput self self.GetIndexForSpendKey self.CalculateOutputKey output

    member private self.CalculateOutputKey (sharedSecret: uint256) (addressIndex: uint32) : Option<uint256> =
        if addressIndex = Coin.UnknownIndex || addressIndex = Coin.CustomKey then
            None
        else
            let sharedSecretHashed =
                let hasher = Hasher HashTags.OUT_KEY
                hasher.Append(sharedSecret.ToBytes() |> BigInt)
                hasher.Hash()
            (calculateSpendKey addressIndex)
                .TweakMul(sharedSecretHashed.ToBytes())
                .ToBytes()
                |> uint256
                |> Some

/// Keychain that doesn't have access to wallet seed, only to private scan key and public spend keys.
/// That is enough to check balance but not enough to spend funds.
type ReadonlyKeychain(privateScanKey: Key, spendPubKeysMap: Collections.Generic.IReadOnlyDictionary<Secp256k1.ECPubKey, uint32>) =
    interface IKeyChain with
        override self.GetStealthAddress(index) = 
            let spendPubKey = (spendPubKeysMap |> Seq.find (fun kvPair -> kvPair.Value = index)).Key
            GetStealthAddress spendPubKey privateScanKey
        
        override self.RewindOutput(output) = 
            let getIndexForPubKey pubKey =
                match spendPubKeysMap.TryGetValue pubKey with
                | (true, key) -> Some key
                | (false, _) -> None
            RewindOutput self getIndexForPubKey (fun _ _ -> None) output
        
        override self.PrivateScanKey = privateScanKey

type Wallet(keyChain: IKeyChain, coins: Map<Hash, Coin>, spentOutputs: Set<Hash>) =
    new(keyChain: IKeyChain) = Wallet(keyChain, Map.empty, Set.empty)

    member self.Coins = coins
    member self.SpentOutputs = spentOutputs

    member self.CanSpend = keyChain :? KeyChain

    member self.AddCoin(coin: Coin) : Wallet =
        Wallet(keyChain, coins |> Map.add coin.OutputId coin, spentOutputs)

    member self.GetCoin(outputId: Hash) : Option<Coin> = 
        coins |> Map.tryFind outputId

    member self.MarkAsSpent(outputId: Hash) : Wallet =
        Wallet(keyChain, coins, spentOutputs |> Set.add outputId)

    member self.GetUnspentCoins(): array<Coin> =
        [| 
            for outputId, coin in coins |> Map.toSeq do
                if coin.IsMine && not(spentOutputs |> Set.contains outputId) then 
                    yield coin 
        |]

    member self.GetBalance() : Amount =
        self.GetUnspentCoins() |> Array.sumBy (fun coin -> coin.Amount)

    member self.RewindOutput(output: Output) : Wallet * Option<Coin> =
        match self.GetCoin(output.GetOutputID()) with
        | Some coin when coin.IsMine -> 
            // If the coin has the spend key, it's fully rewound. If not, try rewinding further.
            if coin.HasSpendKey then
                self, Some coin
            else
                self, keyChain.RewindOutput output
        | _ -> 
            match keyChain.RewindOutput output with
            | Some coin -> self.AddCoin coin, Some coin
            | None -> self, None

    /// Get our coins and spent outputs from transaction (if any) and update the wallet
    member self.ProcessTransaction (transaction: Transaction) : Wallet =
        let updatedWallet =
            transaction.Body.Outputs
            |> Array.fold 
                (fun (wallet: Wallet) output -> wallet.RewindOutput output |> fst)
                self

        transaction.Body.Inputs
        |> Array.fold 
            (fun (wallet: Wallet) input -> 
                if (wallet.GetCoin input.OutputID).IsSome then
                    wallet.MarkAsSpent input.OutputID
                else
                    wallet)
            updatedWallet
    
    /// For given amount, pick enough coins from available coins to cover the amount.
    /// Create recipient from leftover amount if any.
    member private self.GetInputCoinsAndChangeRecipient(totalAmount: Amount) : Option<array<Coin> * Option<Recipient>> =
        let coins = 
            self.GetUnspentCoins() 
            |> Array.sortBy (fun coin -> coin.Amount)
            |> Array.filter (fun coin -> coin.HasSpendKey)

        // 1-based because Array.scan result also includes initial state
        let minCoinsIndex =
            coins 
            |> Array.scan (fun acc coin -> acc + coin.Amount) 0L
            |> Array.tryFindIndex (fun partialSum -> partialSum >= totalAmount)

        match minCoinsIndex with
        | None -> None
        | Some coinsIndex ->
            let inputs = coins |> Array.take coinsIndex
            let inputSum = inputs |> Array.sumBy (fun coin -> coin.Amount)
            let maybeRecipient =
                if inputSum = totalAmount then
                    None
                else
                    { 
                        Amount = inputSum - totalAmount
                        Address = keyChain.GetStealthAddress Coin.ChangeIndex 
                    }
                    |> Some
            Some(inputs, maybeRecipient)

    member private self.Update (transactionOutputs: array<Output>) (spentOutputs: array<Hash>) : Wallet =
        let walletWithCoinsSpent = 
            spentOutputs 
            |> Array.fold 
                (fun (wallet: Wallet) outputId -> wallet.MarkAsSpent outputId) 
                self
        
        transactionOutputs
        |> Array.fold 
            (fun (wallet: Wallet) output -> (wallet.RewindOutput output) |> fst)
            walletWithCoinsSpent

    /// Create MW pegin transaction. Litecoin transaction must have (amount + fee) as its output.
    member self.CreatePegInTransaction (amount: Amount) (fee: Amount) : Wallet * Transaction =
        let recipient = { Amount = amount; Address = keyChain.GetStealthAddress Coin.PeginIndex }
        
        let result =
            TransactionBuilder.BuildTransaction
                Array.empty
                (Array.singleton recipient)
                Array.empty
                (Some(amount + fee))
                fee
        
        let updatedWallet = 
            result.Transaction.Body.Outputs
            |> Array.fold 
                (fun (wallet: Wallet) output -> (wallet.RewindOutput output) |> fst)
                self

        updatedWallet, result.Transaction

    /// Try to create MW to MW transaction using funds in wallet. If there are insufficient funds, return None.
    member self.TryCreateTransaction 
        (amount: Amount) 
        (fee: Amount) 
        (address: StealthAddress) 
        : Option<Wallet * Transaction> =
        let amountWithFee = amount + fee

        match self.GetInputCoinsAndChangeRecipient amountWithFee with
        | None -> None
        | Some (inputCoins, maybeChangeRecipient) ->
            let recipient = { Amount = amount; Address = address }
            let recipients =
                match maybeChangeRecipient with
                | None -> Array.singleton recipient
                | Some changeRecipient -> [| recipient; changeRecipient |]

            let result = 
                TransactionBuilder.BuildTransaction
                    inputCoins
                    recipients
                    Array.empty
                    None
                    fee

            let updatedWallet = 
                self.Update
                    result.Transaction.Body.Outputs
                    (inputCoins |> Array.map (fun coin -> coin.OutputId))

            Some(updatedWallet, result.Transaction)

    /// Try to create pegout transaction using funds in wallet. If there are insufficient funds, return None.
    member self.TryCreatePegOutTransaction 
        (amount: Amount) 
        (fee: Amount) 
        (scriptPubKey: NBitcoin.Script) 
        : Option<Wallet * Transaction> =
        let amountWithFee = amount + fee

        match self.GetInputCoinsAndChangeRecipient amountWithFee with
        | None -> None
        | Some (inputCoins, maybeChangeRecipient) ->
            let pegoutCoin = { Amount = amount; ScriptPubKey = scriptPubKey }
            let recipients =
                match maybeChangeRecipient with
                | None -> Array.empty
                | Some changeRecipient -> Array.singleton changeRecipient

            let result = 
                TransactionBuilder.BuildTransaction
                    inputCoins
                    recipients
                    (Array.singleton pegoutCoin)
                    None
                    fee
            
            let updatedWallet = 
                self.Update
                    result.Transaction.Body.Outputs
                    (inputCoins |> Array.map (fun coin -> coin.OutputId))

            Some(updatedWallet, result.Transaction)
