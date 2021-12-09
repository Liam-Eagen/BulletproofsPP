# BulletproofsPP

#### These protocols and implementations are experimental, have not been reviewed by anyone, and should not be used by anyone for any purpose other than research

## Overview

Bulletproofs++ are a new type of zero knowledge proof based on Bulletproofs and
Bulletproofs+ that are shorter and require fewer elliptic curve operations to
verify. As this is a proof of concept implementation, it isn't possible to say
for certain how much faster verification and proving will be, but for an
equivalently optimized implementation, it is reasonable to believe that
Bulletproofs++ will be faster several times faster to verify than
Bulletproofs(+).

See the paper for more detiled discussion of the protocols. In this repo, I
have currently implemented proofs of concept for 

* Norm-Linear Argument (NormLinearProof)
* Binary Range Proofs (RangeProof.Binary)
* Recirpocal Range Proofs (RangeProof.TypedReciprocal)
* Confidential Transactions (RangeProof.TypedReciprocal)

The implementation of reciprocal range proofs takes advantage of the fact they
are essentially the same as a confidential transaction without the types.

The implementation in TypedReciprocal is slightly less configurable than is
necessary to completely implement the paper. It doesn't drop the multiplicity
commitment in the case of all bases being shared and doesn't drop the types if
there are none. These features should be relatively easy to add.
