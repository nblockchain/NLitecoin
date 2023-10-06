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

    let mimbleRawWimbleTransaction = rawTransaction[Transaction.RegularLTCPeginTranasctionSize *  2 ..]
    let transaction = Transaction.ParseString mimbleRawWimbleTransaction

    Assert.AreEqual(0, transaction.Body.Inputs.Length)
    Assert.AreEqual(1, transaction.Body.Kernels.Length)
    Assert.GreaterOrEqual(transaction.Body.Outputs.Length, 1)

    Assert.IsTrue(transaction.Body.Kernels.[0].Pegin.IsSome)
    Assert.IsEmpty(transaction.Body.Kernels.[0].Pegouts)

    Validation.ValidateTransactionBody transaction.Body
    Validation.ValidateKernelSumForTransaction transaction

[<Test>]
let ParseHogExTransaction () =
    let rawTransaction = IO.File.ReadAllText "transaction2.txt"

    let mimbleRawWimbleTransaction = rawTransaction[Transaction.RegularTransactionOffset * 2 ..]
    let transaction = Transaction.ParseString mimbleRawWimbleTransaction

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

    let mimbleRawWimbleTransaction = rawTransaction[Transaction.RegularTransactionOffset * 2 ..]
    let transaction = Transaction.ParseString mimbleRawWimbleTransaction

    Assert.GreaterOrEqual(transaction.Body.Inputs.Length, 1)
    Assert.AreEqual(1, transaction.Body.Kernels.Length)
    Assert.GreaterOrEqual(transaction.Body.Outputs.Length, 1)

    Assert.IsTrue(transaction.Body.Kernels.[0].Pegin.IsNone)
    Assert.AreEqual(97490L, transaction.Body.Kernels.[0].Pegouts.[0].Amount)

    Validation.ValidateTransactionBody transaction.Body
    Validation.ValidateKernelSumForTransaction transaction