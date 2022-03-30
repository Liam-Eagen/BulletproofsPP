# Bulletproofs++

## Caveats

This project has not been independently reviewed (as of March 2022), and should
be treated as experimental/proof of concept. This true of both the protocols
and the code.

This code makes no attempt to resist any side channel attacks, and is much
slower than Rust implementations of Bulletproofs(+). In the future, I hope to
switch to an FFI/more performant EC library.

## Overview

Bulletproofs++ are a new type of zero knowledge proof based on Bulletproofs and
Bulletproofs+. This code implements Bulletproof++ range proofs and confidential
transactions with multiple types. For detailed information, see the paper.

### Norm Arguments

Bulletproofs use an inner product argument to prove that the inner product of
two committed vectors equals a committed scalar by recursively reducing the size
of the vectors by half. Bulletproofs+ modify this argument to prove that the
value equals the weighted inner product of two vectors. Bulletproofs++ modify
this again to show that the weighted inner product of a vector with itself
equals the committed value while only committing to the vector once.

There are two ways to do this, the first works when the weights are of the same
quadratic residue class as negative one and transforms each weighted difference
of squares into a product. The result is an inner product of two vectors of half
the length, after which a variant of the weighted inner product argument can be
applied.  The other way uses a separate norm argument with a modified round
structure. See paper for details.

Both also support a combined linear argument, where the prover can show that a
linear combination of committed values, plus the norm of the original committed
vector, equals the committed scalar. This allows us to use a new blinding
protocol, where the proof is blinded in a single round with one commitment. The
details are in the paper, but this blinding protocol is responsible for much of
the reduction in proof size.

### Binary Range Proof

The first manner in which Bulletproofs++ differ is in the use of a norm argument
instead of an inner product argument. In Bulletproof(+) range proofs commit to a
vector of binary digits and a vector of their complements and use the inner
product argument to show that each digit times its complement is zero.
Completing the square for each of these multiplications, we can commit to each
digit once and use the norm argument to perform an equivalent check. This
reduces the witness length of binary range proofs by half. Binary range proofs
are implemented in `RangeProof.Binary`.

### Reciprocal Argument

The core of range proofs with larger bases and typed conservation of money is a
permutation argument for multisets. The polynomial permutation argument shows
that two mulitsets `A` and `B` are the same by showing for a random e

`Prod_{(a, m) in A} (e + a)^m = Prod_{(b, m) in B} (e + b)^m`

This works because multiplication is an abelian group and the difference of the
polynomials is only zero at a negligible number of points. Rather than use a
product of monomials, Bulletproofs++ use a sum of reciprocal monomials to
achieve the same effect. This allows including multiplicities, which in the
polynomial case are exponents, as field values.

`Sum_{(a, m) in A} m / (e + a) = Sum_{(b, m) in B} m / (e + b)`

This relation is actually the logarithmic derivative of the polynomial argument.
The structure of the zero knowledge proof protocols follows naturally from this,
the prover first commits to the sets and multiplicities, then the verifier
chooses the challenge value, and the prover commits to the terms in the sum.

### Reciprocal Range Proof

For a base `b` range proof for the value `v = Sum_{i=0..n-1} b^i d_i` with
`m_j` being the multiplicity of the value `j` among the `d_i`, the prover will
show

`Sum_{i=0..n-1} 1/(e + d_i) = Sum_{j=0..b-1} m_j / (e + j)`

There are two types of reciprocal range proofs: in the first the multiplicities
are distinct for each value and in the second multiple aggregated values will
use the same multiplicities.

### Typed Conservation of Money

To show typed conservation of money, the prover wants to show for a set of triples 
`(t,v,o)` where `t` is the type, `v` is the amount, and `o` is zero for inputs and
one for outputs that

`Sum_{(t,v,o)} (-1)^o v/(e + t) = 0`

Since the structure of this proof is so similar to the reciprocal range proofs,
it costs very little to show typed conservation in addition to a range proof.
Both of these protocols are implemented in `RangeProof.TypedReciprocal` which
allows optionally turning on or off various features.

## How to use

The library exposes interfaces for proving and verifying range proofs in
`RangeProof.Binary` (for binary range proofs) and `RangeProof.TypedReciprocal` (for
reciprocal range proofs). There are also interfaces for an abstract norm/linear
argument and implementations using a weighted inner product and a norm argument
in the `Bulletproof` module.

### Arguments

The arguments are of typeclass `BPCommitment` and expose the functions
necessary to collapse the commitment after one round, compute the opening for
verification, etc. They are composable so that two arguments with the same round
structure can be combined to create a compound argument

### Range Proofs

The range proofs are of class `RPCommitment` and expose the functions to prove and
verify range proofs before engaging the Bulletproof argument. They are
parametric over the underlying argument and can be instantiated to use the norm
or inner product argument.

The reciprocal range proofs and confidential transaction are all included in the
RangeProof.TypedReciprocal file, although it does not yet support eliminating
the M commitment for proofs where all the digits are shared. The range proofs
are fairly flexible, supporting typed/conserved transactions, disabling range
proofs and only checking conservation for certain inputs, as well as varying the
base for reciprocal range proofs.

### Command line utility

There is also a command line tool for proving and verifying range proofs of
SECP256k1. The proof is described by a json schema that specifies the various
properties of the proof including the type of proof, whether to do prove
conservation of money, which set of basis points to use, as well as schemas for
the ranges. These include the range [min, max), whether the input is an input or
an output, whether to assume the value lies in the range (for transaction
inputs), as well as several options for reciprocal range proofs including the
base and whether to share the digits. The schema can also specify public inputs
and outputs to the transaction.

The witness is specified via a separate json file, which is a list of objects
specifying the amount, type (for reciprocal range proofs), and optionally a
blinding value for preexisting commitments.

In prove mode, the tool will write out a proof in a binary format to the
specified proof file. This format is not intended to be compatible with
anything, and is minimal in the sense that it includes only the responses and
final openings of the commitments. It cannot be verified without the schema. The
commitments are written to a separate commitment file. In verify mode, the tool
will read from the proof file and commitment file. In test mode, the tool will
run the prover, verify the proof, write the proof and coms to their files, and
then run the verifier.

## Performance

This code is not competitive with implementations in C or Rust or that use
highly performant libraries for the elliptic curve operations. However, it is
possible to estimate the theoretical performance of Bulletproofs++ by counting
the number of elliptic curve operations, as these are by far the most time
consuming part of both proving and verification. By these metrics, a 64 bit
range proof using 16 base 16 digits would require approximately half as many
elliptic curve operations to prove and about 18 percent as many to verify.

Proof size is easy to measure, and for many applications is similarly important
to verification time. The case of the 64 bit range proof is particularly
important in practice, as most cryptocurrencies store amounts using a number of
bits that is approximately 64. For curves where both curve points and scalar are
represented using 32 byte values the proof sizes are

#### 1x64 bit (bytes)
* Bulletproofs: 672
* Bulletproofs+: 576 (Delta 96)
* Bulletproofs++: 416 (Delta 256)

#### 2x64 bit (bytes
* Bulletproofs:   736
* Bulletproofs+:  640 (Delta 96)
* Bulletproofs++: 480 (Delta 256)

## Improvements

There are several features from the paper currently not implemented in code, but
are in the paper

* More Elliptic Curves
* Arithmetic Circuits
* Multiparty Proving
* Batch Verification
* Elimination of the separate multiplicity commitment when all bases are shared.
* Differentiating conserved, as in the amounts sum to zero, from typed
  reciprocal range proofs
* Eliminate the type component in the case types are not used

There are also a bunch of opportunities for improvement. In no particular order
these are

* Transition to using a better (faster/complete/tested) EC library, presumably 
  via FFI bindings.
* Alternatively, implement a pure Haskell EC library that is "good enough."
  Already have some code for finite field operations that is better that
  Integers and mod p after every operation, but a lot of room for improvement.
* In that vein, test performance of using shared/unboxed vectors, depending on
  the EC library. There doesn't seem to be a big difference between lists and
  vectors, but there might be more room for improvement there.
* General performance tuning
* Unit tests
