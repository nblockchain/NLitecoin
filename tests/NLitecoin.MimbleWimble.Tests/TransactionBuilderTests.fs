module NLitecoin.MimbleWimble.TransactionBuilderTests

open NUnit.Framework

open NLitecoin.MimbleWimble
open NLitecoin.MimbleWimble.TransactionBuilder

let GetRandomPubKey() =
    let bytes = NBitcoin.RandomUtils.GetBytes 32
    NBitcoin.Secp256k1.ECPrivKey.Create(bytes).CreatePubKey().ToBytes(true)
    |> BigInt 
    |> PublicKey

let GetRandomStealthAddress() : StealthAddress =
    {
        ScanPubKey = GetRandomPubKey()
        SpendPubKey = GetRandomPubKey()
    }

[<Test>]
let PegInTransactionTest() =
    let amount = 1000L
    let recipient = { Amount = amount; Address = GetRandomStealthAddress() }
    let fee = 100L
    
    let result = 
        TransactionBuilder.BuildTransaction
            Array.empty
            (Array.singleton recipient)
            Array.empty
            (Some(amount + fee))
            fee

    match result.OutputCoins with
    | [| outputCoin |] -> 
        Assert.AreEqual(amount, outputCoin.Amount)
        Assert.AreEqual(Some recipient.Address, outputCoin.Address)
    | _ -> Assert.Fail "Exactly 1 output coin expected"

    Validation.ValidateTransactionBody result.Transaction.Body
    Validation.ValidateKernelSumForTransaction result.Transaction

[<Test>]
let PegOutTransactionTest() =
    let amount = 1000L
    let fee = 100L
    let pegoutCoin = 
        { Amount = amount; ScriptPubKey = NBitcoin.Script.Empty }
    let inputCoin = 
        { Coin.Empty with
            Blind = Some <| BlindingFactor (NBitcoin.RandomUtils.GetUInt256())
            SpendKey = Some (NBitcoin.RandomUtils.GetUInt256())
            Amount = amount + fee }
    
    let result = 
        BuildTransaction
            (Array.singleton inputCoin)
            Array.empty
            (Array.singleton pegoutCoin)
            None
            fee

    Assert.IsEmpty(result.OutputCoins)

    Validation.ValidateTransactionBody result.Transaction.Body
    Validation.ValidateKernelSumForTransaction result.Transaction

[<Test>]
let MWTransactionTest() =
    let amount = 1000L
    let fee = 100L
    let inputCoin = 
        { Coin.Empty with
            Blind = Some <| BlindingFactor (NBitcoin.RandomUtils.GetUInt256())
            SpendKey = Some (NBitcoin.RandomUtils.GetUInt256())
            Amount = amount + fee }
    let recipient = { Amount = amount; Address = GetRandomStealthAddress() }
    
    let result = 
        BuildTransaction
            (Array.singleton inputCoin)
            (Array.singleton recipient)
            Array.empty
            None
            fee

    match result.OutputCoins with
    | [| outputCoin |] -> 
        Assert.AreEqual(amount, outputCoin.Amount)
        Assert.AreEqual(Some recipient.Address, outputCoin.Address)
    | _ -> Assert.Fail "Exactly 1 output coin expected"

    Validation.ValidateTransactionBody result.Transaction.Body
    Validation.ValidateKernelSumForTransaction result.Transaction

[<Test>]
let MWTransactionTest2() =
    // send part of the funds
    let balance = 3000L
    let amount = 1000L
    let fee = 100L
    let inputCoin = 
        { Coin.Empty with
            Blind = Some <| BlindingFactor (NBitcoin.RandomUtils.GetUInt256())
            SpendKey = Some (NBitcoin.RandomUtils.GetUInt256())
            Address = Some(GetRandomStealthAddress())
            Amount = balance }
    let recipient = { Amount = amount; Address = GetRandomStealthAddress() }
    let recipientUnspent = { Amount = balance - amount - fee; Address = GetRandomStealthAddress() }
    
    let result = 
        BuildTransaction
            (Array.singleton inputCoin)
            [| recipient; recipientUnspent |]
            Array.empty
            None
            fee

    match result.OutputCoins with
    | [| outputCoin; outputCoinUnspent |] -> 
        Assert.AreEqual(amount, outputCoin.Amount)
        Assert.AreEqual(Some recipient.Address, outputCoin.Address)
        Assert.AreEqual(recipientUnspent.Amount, outputCoinUnspent.Amount)
        Assert.AreEqual(Some recipientUnspent.Address, outputCoinUnspent.Address)
    | _ -> Assert.Fail "Exactly 2 output coins expected"

    Validation.ValidateTransactionBody result.Transaction.Body
    Validation.ValidateKernelSumForTransaction result.Transaction

[<Test>]
let InvalidTransactionsTest() =
    let amount = 1000L
    let recipient = { Amount = amount; Address = GetRandomStealthAddress() }
    let fee = 100L
    
    Assert.Throws<IncorrectBalanceException>
        (fun _ ->
            BuildTransaction
                Array.empty
                (Array.singleton recipient)
                Array.empty
                (Some amount) // fee should be added here, but it's not
                fee
            |> ignore)
        |> ignore
