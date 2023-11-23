module NLitecoin.MimbleWimble.ZKPTests

// Differential tests for zero-knowledge proof components that use https://github.com/tangramproject/Secp256k1-ZKP.Net as reference

open System
open System.Runtime.InteropServices

open NUnit.Framework
open FsCheck
open FsCheck.NUnit
open Org.BouncyCastle.Math
open NBitcoin

open NLitecoin.MimbleWimble
open NLitecoin.MimbleWimble.EC

type ByteArray32Generators =
    static member ByteArray() =
        { new Arbitrary<array<byte>>() with
            override _.Generator =
                Gen.arrayOfLength 32 (Gen.choose(0, 255) |> Gen.map byte)  }

    static member UInt256() =
        { new Arbitrary<uint256>() with
            override _.Generator =
                Arb.generate<array<byte>> |> Gen.map uint256  }
    
    static member BlindingFactor() =
        { new Arbitrary<BlindingFactor>() with
            override _.Generator =
                gen {
                    let! bytes = Arb.generate<array<byte>>
                    let! leadingZeros = Gen.elements [ 0; 0; 0; 1; 31 ]
                    Array.fill bytes 0 leadingZeros 0uy
                    return bytes |> NBitcoin.uint256 |> BlindingFactor } }

type private Secp256k1ZKpBulletproof() =
    inherit Secp256k1ZKP.Net.BulletProof()

    [<DllImport("libsecp256k1", CallingConvention = CallingConvention.Cdecl)>]
    static extern uint64 secp256k1_bulletproof_innerproduct_proof_length(uint64 n)

    [<DllImport("libsecp256k1", CallingConvention = CallingConvention.Cdecl)>]
    static extern int secp256k1_generator_generate(nativeint ctx, IntPtr gen, byte[] key32)

    [<DllImport("libsecp256k1", CallingConvention = CallingConvention.Cdecl)>]
    static extern int secp256k1_generator_serialize(nativeint ctx, byte[] output, IntPtr gen)

    member self.InnerproductProofLength(n: uint64) : uint64 =
        secp256k1_bulletproof_innerproduct_proof_length(n)

    member self.GeneratorGenerate(key: array<byte>) =
        let gen = Marshal.AllocHGlobal 64
        let opResult = secp256k1_generator_generate(self.Context, gen, key)
        assert(opResult <> 0)
        assert(gen <> IntPtr.Zero)
        let output = Array.zeroCreate<byte> 33
        let opResult2 = secp256k1_generator_serialize(self.Context, output, gen)
        assert(opResult2 <> 0)
        Marshal.FreeHGlobal gen
        output

[<Test>]
let TestSchnorrSign () =
    let test message key expected =
        let signature = SchnorrSign key message
        let signatureBytes = 
            match signature with
            | Signature bigint -> bigint.Data
        Assert.AreEqual(expected, signatureBytes)

    // Test vectors (see https://github.com/litecoin-project/litecoin/blob/5ac781487cc9589131437b23c69829f04002b97e/src/secp256k1-zkp/src/modules/schnorrsig/tests_impl.h#L168)
    let key1 = Array.zeroCreate 32 |> Array.updateAt 31 1uy
    let msg1 = Array.zeroCreate 32
    let expected1 = 
        "787A848E71043D280C50470E8E1532B2DD5D20EE912A45DBDD2BD1DFBF187EF67031A98831859DC34DFFEEDDA86831842CCD0079E1F92AF177F7F22CC1DCED05"
        |> Convert.FromHexString
    
    test msg1 key1 expected1

    let key2 = "B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF" |> Convert.FromHexString
    let msg2 = "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89" |> Convert.FromHexString
    let expected2 = 
        "2A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D1E51A22CCEC35599B8F266912281F8365FFC2D035A230434A1A64DC59F7013FD"
        |> Convert.FromHexString

    test msg2 key2 expected2

    let key3 = "C90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C7" |> Convert.FromHexString
    let msg3 = "5E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C" |> Convert.FromHexString
    let expected3 = 
        "00DA9B08172A9B6F0466A2DEFD817F2D7AB437E0D253CB5395A963866B3574BE00880371D01766935B92D2AB4CD5C8A2A5837EC57FED7660773A05F0DE142380"
        |> Convert.FromHexString

    test msg3 key3 expected3

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestPedersenCommit (value: uint64) (blind: BlindingFactor) =
    blind.ToUInt256() <> uint256.Zero ==> fun () ->
        use pedersen = new Secp256k1ZKP.Net.Pedersen()
        let referenceCommitment = pedersen.Commit(value, blind.ToUInt256().ToBytes())
        let ourCommitment = Pedersen.Commit (int64 value) blind
        ourCommitment = PedersenCommitment(BigInt referenceCommitment)

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestBlindSwitch (value: uint64) (blind: BlindingFactor) =
    blind.ToUInt256() <> uint256.Zero ==> fun () ->
        use pedersen = new Secp256k1ZKP.Net.Pedersen()
        let referenceBlind = pedersen.BlindSwitch(value, blind.ToUInt256().ToBytes())
        let ourBlind = Pedersen.BlindSwitch blind (int64 value)
        ourBlind = BlindingFactor(uint256 referenceBlind)

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestBlindingFactor (factor: BlindingFactor) =
    let bytes = factor.ToUInt256().ToBytes()
    (bytes |> BigInteger.FromByteArrayUnsigned |> EC.curve.Curve.FromBigInteger).GetEncoded() = bytes

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestBigIntegerToUInt256 (bytes: array<byte>) =
    let integer = bytes |> BigInteger.FromByteArrayUnsigned
    integer = (integer.ToUInt256().ToBytes() |> Org.BouncyCastle.Math.BigInteger.FromByteArrayUnsigned)

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestByteArrayToUInt256 (bytes: array<byte>) =
    bytes = (bytes |> uint256).ToBytes()

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestAddBlindingFactors (positive: array<BlindingFactor>) (negative: array<BlindingFactor>) =
    use pedersen = new Secp256k1ZKP.Net.Pedersen()
    let referenceSum = 
        pedersen.BlindSum(
            positive |> Array.map (fun each -> each.ToUInt256().ToBytes()),
            negative |> Array.map (fun each -> each.ToUInt256().ToBytes())
        )
    let ourSum = Pedersen.AddBlindingFactors positive negative
    ourSum.ToUInt256().ToBytes() = referenceSum

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|], MaxTest=20)>]
let TestRangeProofCanBeVerified 
    (amount: uint64) 
    (key: uint256) 
    (privateNonce: uint256) 
    (rewindNonce: uint256)
    (extraData: Option<array<byte>>) =
    
    let commit = 
        match Pedersen.Commit (int64 amount) (BlindingFactor <| key) with
        | PedersenCommitment num -> num.Data

    let proofMessage = Array.zeroCreate 20
    let proof = Bulletproof.ConstructRangeProof amount key privateNonce rewindNonce proofMessage extraData
    let proofData = 
        match proof with
        | RangeProof data -> data
    
    let extraDataAsNullable =
        match extraData with
        | Some array -> array
        | None -> null

    use secp256k1ZKPBulletProof = new Secp256k1ZKpBulletproof()
    // argument names are wrong here: 3rd param should be rewindNonce and 4th nonce
    //let proofZKP = secp256k1ZKPBulletProof.ProofSingle(amount, key.ToBytes(), rewindNonce.ToBytes(), privateNonce.ToBytes(), extraDataAsNullable, proofMessage)

    secp256k1ZKPBulletProof.Verify(commit, proofData, extraDataAsNullable)

[<Test>]
let TestInnerproductProofLength() =
    use secp256k1ZKPBulletProof = new Secp256k1ZKpBulletproof()
    try
        for exp=0 to 16 do
            let n = pown 2 (int exp)
            let ourLength = Bulletproof.InnerProductProofLength(int n)
            let referenceLength = secp256k1ZKPBulletProof.InnerproductProofLength(uint64 n)
            Assert.AreEqual(referenceLength, uint64 ourLength)
    with
    | :? System.EntryPointNotFoundException ->
        Assert.Inconclusive "no secp256k1_bulletproof_innerproduct_proof_length in libsecp256k1 on Linux"

[<Property(Arbitrary=[|typeof<ByteArray32Generators>|])>]
let TestGeneratorGenerate(key: array<byte>) =
    use secp256k1ZKPBulletProof = new Secp256k1ZKpBulletproof()
    let referenceGenerator = secp256k1ZKPBulletProof.GeneratorGenerate key
    
    let ourGenerator = Bulletproof.GeneratorGenerate key
    let ourGeneratorSerialized = ourGenerator.GetEncoded true
    
    // skip first byte since serialization formats are different
    referenceGenerator.[1..] = ourGeneratorSerialized.[1..]

[<Test>]
let TestRfc6979HmacSha256() =
    // output from modified secp256k1-zkp tests
    // first 2 keys generated in secp256k1_bulletproof_generators_create
    // from generatorG as seed
    let referenceKeys =
        [| 
            "edc883a98f9ad8dad390a2c814647b6dac92aed530da554db914ea4f8ad988c7"
            "d99994e5535e0788752493113103145529e20b38e1c68dc28f67816b2a85b65f"
        |]
        |> Array.map(fun str -> Convert.FromHexString str)

    let ourKeys =
        let seed = Array.append (generatorG.XCoord.GetEncoded()) (generatorG.YCoord.GetEncoded())
        let rng = Bulletproof.Rfc6979HmacSha256 seed
        Array.init 2 (fun _ -> rng.Generate 32)

    Array.iter2 
        (fun refKey ourKey -> Assert.AreEqual(refKey, ourKey))
        referenceKeys
        ourKeys

[<Test>]
let TestScalarChaCha20() =
    // see https://github.com/litecoin-project/litecoin/blob/5ac781487cc9589131437b23c69829f04002b97e/src/secp256k1-zkp/src/tests.c#L1010
    let seed1 = uint256(Array.zeroCreate<byte> 32)

    let expected1l =
        [|
            0x76uy; 0xb8uy; 0xe0uy; 0xaduy; 0xa0uy; 0xf1uy; 0x3duy; 0x90uy
            0x40uy; 0x5duy; 0x6auy; 0xe5uy; 0x53uy; 0x86uy; 0xbduy; 0x28uy
            0xbduy; 0xd2uy; 0x19uy; 0xb8uy; 0xa0uy; 0x8duy; 0xeduy; 0x1auy
            0xa8uy; 0x36uy; 0xefuy; 0xccuy; 0x8buy; 0x77uy; 0x0duy; 0xc7uy
        |]
        |> BigInteger.FromByteArrayUnsigned
    let expected1r =
        [|
            0xdauy; 0x41uy; 0x59uy; 0x7cuy; 0x51uy; 0x57uy; 0x48uy; 0x8duy
            0x77uy; 0x24uy; 0xe0uy; 0x3fuy; 0xb8uy; 0xd8uy; 0x4auy; 0x37uy
            0x6auy; 0x43uy; 0xb8uy; 0xf4uy; 0x15uy; 0x18uy; 0xa1uy; 0x1cuy
            0xc3uy; 0x87uy; 0xb6uy; 0x69uy; 0xb2uy; 0xeeuy; 0x65uy; 0x86uy
        |]
        |> BigInteger.FromByteArrayUnsigned

    Assert.Less(expected1l, scalarOrder)
    Assert.Less(expected1r, scalarOrder)

    let l, r = Bulletproof.ScalarChaCha20 seed1 0UL

    Assert.AreEqual(expected1l, l)
    Assert.AreEqual(expected1r, r)

    let expected2l =
        [|
            0x45uy; 0x40uy; 0xf0uy; 0x5auy; 0x9fuy; 0x1fuy; 0xb2uy; 0x96uy
            0xd7uy; 0x73uy; 0x6euy; 0x7buy; 0x20uy; 0x8euy; 0x3cuy; 0x96uy
            0xebuy; 0x4fuy; 0xe1uy; 0x83uy; 0x46uy; 0x88uy; 0xd2uy; 0x60uy
            0x4fuy; 0x45uy; 0x09uy; 0x52uy; 0xeduy; 0x43uy; 0x2duy; 0x41uy
        |]
        |> BigInteger.FromByteArrayUnsigned
    let expected2r =
        [|
            0xbbuy; 0xe2uy; 0xa0uy; 0xb6uy; 0xeauy; 0x75uy; 0x66uy; 0xd2uy
            0xa5uy; 0xd1uy; 0xe7uy; 0xe2uy; 0x0duy; 0x42uy; 0xafuy; 0x2cuy
            0x53uy; 0xd7uy; 0x92uy; 0xb1uy; 0xc4uy; 0x3fuy; 0xeauy; 0x81uy
            0x7euy; 0x9auy; 0xd2uy; 0x75uy; 0xaeuy; 0x54uy; 0x69uy; 0x63uy
        |]
        |> BigInteger.FromByteArrayUnsigned

    let seed2 = seed1.ToBytes() |> Array.updateAt 31 1uy |> uint256
    let l2, r2 = Bulletproof.ScalarChaCha20 seed2 0UL

    Assert.AreEqual(expected2l, l2)
    Assert.AreEqual(expected2r, r2)

    let expected3l =
        [|
            0x47uy; 0x4auy; 0x4fuy; 0x35uy; 0x4fuy; 0xeeuy; 0x93uy; 0x59uy
            0xbbuy; 0x65uy; 0x81uy; 0xe5uy; 0xd9uy; 0x15uy; 0xa6uy; 0x01uy
            0xb6uy; 0x8cuy; 0x68uy; 0x03uy; 0x38uy; 0xffuy; 0x65uy; 0xe6uy
            0x56uy; 0x4auy; 0x3euy; 0x65uy; 0x59uy; 0xfcuy; 0x12uy; 0x3fuy
        |]
        |> BigInteger.FromByteArrayUnsigned
    let expected3r =
        [|
            0xa9uy; 0xb2uy; 0xf9uy; 0x3euy; 0x57uy; 0xc3uy; 0xa5uy; 0xcbuy
            0xe0uy; 0x72uy; 0x74uy; 0x27uy; 0x88uy; 0x1cuy; 0x23uy; 0xdfuy
            0xe2uy; 0xb6uy; 0xccuy; 0xfbuy; 0x93uy; 0xeduy; 0xcbuy; 0x02uy
            0xd7uy; 0x50uy; 0x52uy; 0x45uy; 0x84uy; 0x88uy; 0xbbuy; 0xeauy
        |]
        |> BigInteger.FromByteArrayUnsigned

    let l3, r3 = Bulletproof.ScalarChaCha20 seed2 100UL

    Assert.AreEqual(expected3l, l3)
    Assert.AreEqual(expected3r, r3)

[<Test>]
let TestUpdateCommit() =
    // output from modified secp256k1-zkp tests
    let commit = 
        "ea47aaa6e111d44f973cffff730dc3f5a41cd1d30687bbfcd8b91ad8fc9d63e6" 
        |> Convert.FromHexString
        |> uint256
    let lpt = 
        let x = "2dc4b4f3b3d9530c5d1ab2d7fe12291be0aa7c4a0b5ccf6125c958a2867d652a"
        let y = "6d5e07c347e778672126cb47a8a26d40e84b0639805b219c129c1f34be51a8ba"
        curve.Curve.CreatePoint(BigInteger(x, 16), BigInteger(y, 16))
    let rpt = 
        let x = "62a7bb4d9ab0ff01363368093354af7941d058ebd16a1cd3bd21cfc6401d5112"
        let y = "44f98a209695e93c28e4293dd9cb113affa4d92e8f1dbdb907d8bcb6271617a9"
        curve.Curve.CreatePoint(BigInteger(x, 16), BigInteger(y, 16))

    let expected = 
        "8370c779a784b2188e14f5bf5f936df110361f0fbefee873c9a75e8d928cf4d9"
        |> Convert.FromHexString
        |> uint256

    Assert.AreEqual(expected, Bulletproof.UpdateCommit commit lpt rpt)
