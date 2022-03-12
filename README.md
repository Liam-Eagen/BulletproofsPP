# BulletproofsPP

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
of the vectors by half. Bulletproofs+ modify this arugment to prove that the
value equals the weighted inner product of two vectors. Bulletproofs++ modify
this again to show that the weighted inner product of a vector with itself
equals the committed value while only committing to the vector once.

There are two ways to do this, the first works when the weightes are of the same
quadratic residue class as negative one and transforms each weighted difference
of squares into a product. The result is an inner product of two vectors of half
the length, after which a variant of the weighted inner product argument can be
applied.  The other way uses a seperate norm argument with a modified round
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
digit once and use the norm arugment to perform an equivalent check. This
reduces the witness length of binary range proofs by half.

### Reciprocal Range Proof

Bulletproofs++ also differ from the earlier protocols in that they support range
proofs with larger bases than 2. At a high level, the way this is possible is by
encoding the digits of a value in base b as the roots of a polynomial. Taking
the logarithmic deriviative of the polynomial, we can write the rational
function in two ways, first as a sum of reciprocal monomials corresponding to
each digit of the value and then as a sum of public symbol values times the
multiplicity of the symbol in the value.

There are two ways to show this in a zero knowledge proof, first using a
different set of symbols and multiplicities for each value and also using a
shared set of symbols and multiplicities. For smaller numbers of values, the
first is preferable for technical reasons, but for larger numbers of values the
shared digits can acheive significantly reduced witness and proof sizes.

### Typed Conservation of Money

When used in cryptocurrencies, range proofs are typically used to perform
confidential transactions, where the amounts involved in the transaction are
hidden from public view. Transaction correctness is established via a zero
knowledge proof of conservation of money, which shows that the amount flowing
into a transaction is equal to the amount flowing out of a transaction. Range
proofs are necessary to show that all of these amounts of money are positive
integers.

The same reciprocal technique used by the range proof is then used to construct
a proof of conservation of money for multiplie types of money that is zero
knowledge in the types, the number of types, and the relationships between the
types of different values. That is, zero knowledge up to whatever is publically
known about the transaction (i.e. if a fee of type t is payed, at least one
input must be of type t, it there is only one output all the inputs must be the
same type, etc.) 

## How to use

The library exposes interfaces for proving and verifying range proofs in
RangeProof.Binary (for binary range proofs) and RangeProof.TypedReciprocal (for
reciprocal range proofs).

### Arguments

The arguments are of the typeclass BPCommitment and expose the functions
necessary to collapse the commitment after one round, compute the opening for
verification, etc. They are composable so that two arguments with the same round
structure can be combined to create a compound argument

### Range Proofs

The range proofs are of class RPCommitment and expose the function to prove and
verify range proofs before engaging the bulletproof argument. They are
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
SECP256k1. The proof is described by a json schema that describes the various
properties of the proof including the type of proof, whether to do prove
conservation of money, which set of basis points to use, as well as schemas for
the ranges. These include the range [min, max), whether the input is an input or
an output, whether to assume the value lies in the range (for transaction
inputs), as well as several options for reciprocal range proofs including the
base and whether to share the digits. The schema can also specify public inputs
and outputs to the transaction.

The witness is specified via a seperate json file, which is a list of objects
specifying the amount, type (for reciprocal range proofs), and optionally a
blinding value for preexisting commitments.

In prove mode, the tool will write out a proof in a binary format to the
specified proof file. This format is not intended to be compatible with
anything, and is minimal in the sense that it includes only the responses and
final openings of the commitments. It cannot be verified without the schema. The
commitments are written to a seperate commitment file. In verify mode, the tool
will read from the proof file and commitment file. In test mode, the tool will
run the prover, verify the proof, write the proof and coms to their files, and
then run the verifier.

## Performance

This code is not competitive with implementations in C or Rust or that use
highly performant libraries for the elliptic curve operations. However, it is
possible to roughly estimate the theoretical performance of Bulletproofs++ by
counting the number of elliptic curve operations, as these are by far the most
time consuming part of both proving and verification. By these metrics, a 64 bit
range proof using 16 base 16 digits would require approximately half as many
elliptic curve operations to prove and about 18 percent as many to verify.

Proof size is easy to measure, and for many applications is similarly important
to verification time. The case of the 64 bit range proof is particularly
important in practice, as most cryptocurrencies store amounts using a number of
bits that is approximately 64.

#### 1x64 bit (bytes)
Bulletproofs: 672
Bullteproofs+: 576 (Delta 96)
Bulletproofs++: 416 (Delta 256)

#### 2x64 bit (bytes
Bulletproofs:   736
Bulletproofs+:  640 (Delta 96)
Bulletproofs++: 480 (Delta 256)

## Improvements

There are several features from the paper currently not implemented in code, but
are in the paper

* Arithmetic Circuits
* Multiparty Proving
* Batch Verification
* Eliminaton of the seperate multiplicity commitment when all bases are shared.
* Differentiating conserved, as in the amounts sum to zero, from typed
  reciprocal range proofs. Also, eliminate the type component in the case types
  are not used.

There are also a bunch of opportunities for improvement. In no particular order
these are

* Transition to using a better (faster/complete/tested) EC library, presumably 
  via FFI bindings.
* Alternatively, implement a pure Haskell EC library that is ``good enough."
  Already have some code for finite field operations that is better that
  Integers and mod p after every operation, but a lot of room for improvement.
* In that vein, test performance of using shared/unboxed vectors, depending on
  the EC library. There doesn't seem to be a big difference between lists and
  vectors, but there might be more room for improvement there.
* General performance tuning
* Unit tests
