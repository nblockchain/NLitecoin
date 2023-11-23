module NLitecoin.MimbleWimble.WalletTests

open NUnit.Framework

open NBitcoin

open NLitecoin.MimbleWimble
open NLitecoin.MimbleWimble.Wallet

// see https://github.com/litecoin-project/litecoin/blob/5ac781487cc9589131437b23c69829f04002b97e/src/wallet/test/scriptpubkeyman_tests.cpp#L44
let walletSeed =
    let key = 
        let data = 
            DataEncoders.Base58CheckEncoder().DecodeData("6usgJoGKXW12i7Ruxy8Z1C5hrRMVGfLmi9NU9uDQJMPXDJ6tQAH")
        new Key(data.[1..32], 32, false)
    key.ToBytes()

[<Test>]
let TestKeyDerivation() =
    let keyChain = KeyChain walletSeed

    Assert.AreEqual(
        "2396e5c33b07dfa2d9e70da1dcbdad0ad2399e5672ff2d4afbe3b20bccf3ba1b", 
        keyChain.SpendKey.PrivateKey.ToHex())
    Assert.AreEqual(
        "918271168655385e387907612ee09d755be50c4685528f9f53eabae380ecba97", 
        keyChain.ScanKey.PrivateKey.ToHex())

[<Test>]
let TestStealthAddressGeneration() =
    let keyChain = KeyChain walletSeed

    let changeAddress = keyChain.GetStealthAddress 0u
    Assert.AreEqual(
        "ltcmweb1qq20e2arnhvxw97katjkmsd35agw3capxjkrkh7dk8d30rczm8ypxuq329nwh2twmchhqn3jqh7ua4ps539f6aazh79jy76urqht4qa59ts3at6gf",
        changeAddress.EncodeDestination())

    let peginAddress = keyChain.GetStealthAddress 1u
    Assert.AreEqual(
        "ltcmweb1qqg5hddkl4uhspjwg9tkmatxa4s6gswdaq9swl8vsg5xxznmye7phcqatzc62mzkg788tsrfcuegxe9q3agf5cplw7ztqdusqf7x3n2tl55x4gvyt",
        peginAddress.EncodeDestination())

    let receiveAddress = keyChain.GetStealthAddress 2u
    Assert.AreEqual(
        "ltcmweb1qq0yq03ewm830ugmkkvrvjmyyeslcpwk8ayd7k27qx63sryy6kx3ksqm3k6jd24ld3r5dp5lzx7rm7uyxfujf8sn7v4nlxeqwrcq6k6xxwqdc6tl3",
        receiveAddress.EncodeDestination())

[<Test>]
let TestWallet() =
    let keyChain = KeyChain walletSeed
    let wallet = Wallet keyChain
    
    let initialAmount = 10000L
    let fee = 100L

    let walletAfterPegin, peginTx = wallet.CreatePegInTransaction initialAmount fee
    Assert.AreEqual(initialAmount, walletAfterPegin.GetBalance())

    let payment1Amount = 2000L
    let payment1Address = TransactionBuilderTests.GetRandomStealthAddress()
    let walletAfterPayment1, payment1Tx = 
        (walletAfterPegin.TryCreateTransaction payment1Amount fee payment1Address).Value
    Assert.AreEqual(initialAmount - fee - payment1Amount, walletAfterPayment1.GetBalance())
    
    // not enough funds
    Assert.AreEqual(None, walletAfterPayment1.TryCreateTransaction initialAmount fee payment1Address)
    Assert.AreEqual(None, walletAfterPayment1.TryCreatePegOutTransaction initialAmount fee Script.Empty)

    let pegOutAmount = 3000L
    let walletAfterPegOut, pegOutTx = 
        (walletAfterPayment1.TryCreatePegOutTransaction pegOutAmount fee Script.Empty).Value
    Assert.AreEqual(initialAmount - fee - payment1Amount - fee - pegOutAmount, walletAfterPegOut.GetBalance())

    let walletRestoredFromTransactions = 
        [ peginTx; payment1Tx; pegOutTx ]
        |> List.fold 
            (fun (currWallet: Wallet) tx -> currWallet.ProcessTransaction tx)
            wallet

    Assert.AreEqual(walletAfterPegOut.GetBalance(), walletRestoredFromTransactions.GetBalance())
    CollectionAssert.AreEquivalent(walletAfterPegOut.GetUnspentCoins(), walletRestoredFromTransactions.GetUnspentCoins())
