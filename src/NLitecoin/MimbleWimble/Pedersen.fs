module NLitecoin.MimbleWimble.Pedersen

open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Asn1.X9
open Org.BouncyCastle.Math
open NBitcoin

open EC

// https://github.com/litecoin-project/litecoin/blob/5ac781487cc9589131437b23c69829f04002b97e/src/secp256k1-zkp/src/modules/commitment/main_impl.h#L41
let SerializeCommitment (commitment: ECPoint) =
    let bytes = 
        if commitment.IsInfinity || (commitment.XCoord.IsZero && commitment.YCoord.IsZero) then
            Array.zeroCreate PedersenCommitment.NumBytes
        else
            commitment.GetEncoded true
    bytes.[0] <- 9uy ^^^ (if EC.IsQuadVar (commitment.Normalize().YCoord) then 1uy else 0uy)
    bytes

let DeserializeCommitment (commitment: PedersenCommitment) : ECPoint =
    let x = commitment.ToBytes() |> Array.skip 1 |> BigInteger.FromByteArrayUnsigned |> curve.Curve.FromBigInteger
    let y = x.Square().Multiply(x).Add(curve.Curve.B).Sqrt()
    let point = curve.Curve.CreatePoint(x.ToBigInteger(), y.ToBigInteger())
    if commitment.ToBytes().[0] &&& 1uy <> 0uy then
        point.Negate()
    else
        point

/// Generates a pedersen commitment: *commit = blind * G + value * H. The blinding factor is 32 bytes.
let Commit (value: Amount) (blind: BlindingFactor) : PedersenCommitment =
    let result =
        let blind = blind.ToUInt256().ToBytes() |> BigInteger.FromByteArrayUnsigned
        let a = generatorG.Multiply(blind)
        let b = generatorH.Multiply(BigInteger.ValueOf value)
        a.Add b
    let bytes = SerializeCommitment result
    assert(bytes.Length = PedersenCommitment.NumBytes)
    PedersenCommitment(BigInt bytes)

/// Calculates the blinding factor x' = x + SHA256(xG+vH | xJ), used in the switch commitment x'G+vH.
let BlindSwitch (blindingFactor: BlindingFactor) (amount: Amount) : BlindingFactor =
    let hasher = Sha256Digest()

    let x = blindingFactor.ToUInt256().ToBytes() |> BigInteger.FromByteArrayUnsigned
    /// xG + vH
    let commit = Commit amount blindingFactor
    let commitSerialized = match commit with | PedersenCommitment num -> num.Data
    hasher.BlockUpdate(commitSerialized, 0, commitSerialized.Length)

    // xJ
    let xJ = generatorJPub.Multiply(x)
    let xJSerialized = xJ.GetEncoded true
    hasher.BlockUpdate(xJSerialized, 0, xJSerialized.Length)

    let hash = Array.zeroCreate<byte> 32
    hasher.DoFinal(hash, 0) |> ignore

    let result = x.Add((hash |> BigInteger.FromByteArrayUnsigned).Mod(EC.curve.Curve.Field.Characteristic)).Mod(scalarOrder)
    
    result.ToUInt256()
    |> BlindingFactor

let AddBlindingFactors (positive: array<BlindingFactor>) (negative: array<BlindingFactor>) : BlindingFactor =
    let sum (factors: array<BlindingFactor>) = 
        factors
        |> Array.map (fun blind -> blind.ToUInt256().ToBytes() |> BigInteger.FromByteArrayUnsigned)
        |> Array.fold (fun (a : BigInteger) b -> a.Add b) BigInteger.Zero
    
    let result = (sum positive).Subtract(sum negative).Mod(scalarOrder)
    
    result.ToUInt256()
    |> BlindingFactor

let AddCommitments (positive: array<PedersenCommitment>) (negative: array<PedersenCommitment>) : PedersenCommitment =
    let sum (commitments: array<PedersenCommitment>) = 
        commitments
        |> Array.map DeserializeCommitment
        |> Array.fold (fun (a : ECPoint) b -> a.Add b) (generatorG.Multiply BigInteger.Zero)
    
    let result = (sum positive).Subtract(sum negative)
    
    result |> SerializeCommitment |> BigInt |> PedersenCommitment
