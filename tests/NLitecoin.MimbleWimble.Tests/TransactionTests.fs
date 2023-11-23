module NLitecoin.MimbleWimble.TransactionTests

open System

open NUnit.Framework

open NLitecoin.MimbleWimble

[<SetUp>]
let Setup () =
    ()

[<Test>]
let ParsePegInTransaction () =
    let rawTransaction = IO.File.ReadAllText "transaction1.txt"

    let litecoinTransaction = 
        NBitcoin.Transaction.Parse(rawTransaction, NLitecoin.Litecoin.Instance.Mainnet)

    let transaction = 
        (litecoinTransaction :?> NLitecoin.LitecoinTransaction).MimbleWimbleTransaction.Value

    Assert.AreEqual(0, transaction.Body.Inputs.Length)
    Assert.AreEqual(1, transaction.Body.Kernels.Length)
    Assert.GreaterOrEqual(transaction.Body.Outputs.Length, 1)

    Assert.IsTrue(transaction.Body.Kernels.[0].Pegin.IsSome)
    Assert.IsEmpty(transaction.Body.Kernels.[0].Pegouts)

    Validation.ValidateTransactionBody transaction.Body
    Validation.ValidateKernelSumForTransaction transaction

[<Test>]
let ParseMWTransaction () =
    let rawTransaction = IO.File.ReadAllText "transaction2.txt"

    let litecoinTransaction = 
        NBitcoin.Transaction.Parse(rawTransaction, NLitecoin.Litecoin.Instance.Mainnet)

    let transaction = 
        (litecoinTransaction :?> NLitecoin.LitecoinTransaction).MimbleWimbleTransaction.Value

    Assert.GreaterOrEqual(transaction.Body.Inputs.Length, 1)
    Assert.AreEqual(1, transaction.Body.Kernels.Length)
    Assert.GreaterOrEqual(transaction.Body.Outputs.Length, 1)

    Assert.IsTrue(transaction.Body.Kernels.[0].Pegin.IsNone)
    Assert.IsEmpty(transaction.Body.Kernels.[0].Pegouts)

    Validation.ValidateTransactionBody transaction.Body
    Validation.ValidateKernelSumForTransaction transaction

[<Test>]
let ParsePegOutTransaction () =
    let rawTransaction = IO.File.ReadAllText "transaction3.txt"

    let litecoinTransaction = 
        NBitcoin.Transaction.Parse(rawTransaction, NLitecoin.Litecoin.Instance.Mainnet)

    let transaction = 
        (litecoinTransaction :?> NLitecoin.LitecoinTransaction).MimbleWimbleTransaction.Value

    Assert.GreaterOrEqual(transaction.Body.Inputs.Length, 1)
    Assert.AreEqual(1, transaction.Body.Kernels.Length)
    Assert.GreaterOrEqual(transaction.Body.Outputs.Length, 1)

    Assert.IsTrue(transaction.Body.Kernels.[0].Pegin.IsNone)
    Assert.AreEqual(97490L, transaction.Body.Kernels.[0].Pegouts.[0].Amount)

    Validation.ValidateTransactionBody transaction.Body
    Validation.ValidateKernelSumForTransaction transaction

[<Test>]
let ParseBlockWithHogExTransaction () =
    // Check if HogEx transaction, which has mweb extension flag but doesn't contain MW transaction, is pardsed correctly
    let blockData = IO.File.ReadAllText "block1.txt"
    let block = NBitcoin.Block.Parse(blockData, NLitecoin.Litecoin.Instance.Mainnet)
    // HogEx transaction must be at the end of the block
    // (see https://github.com/litecoin-project/lips/blob/master/lip-0002.mediawiki#user-content-Integrating_Transaction_ExtTxn)
    let lastTransaction = block.Transactions.[block.Transactions.Count - 1] :?> NLitecoin.LitecoinTransaction
    Assert.IsTrue(lastTransaction.MimbleWimbleTransaction.IsNone)
