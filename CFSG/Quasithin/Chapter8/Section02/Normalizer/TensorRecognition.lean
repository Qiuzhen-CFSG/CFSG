module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Kernel
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CoreAction
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Cubic
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Dihedral
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CodeObstruction

/-!
# Tensor recognition in the normalizer of U

Source: Aschbacher–Smith, Proposition 8.2.8(3–6), printed pp.718–719
(PDF pp.735–736). This module exports completed conditional steps, not the
full proposition.

The canonical conjugation action on the literal P/U has its kernel computed
from the earlier kernel on B/U, two-conjugate generation and the commutator
bound. Its faithful action image has a marked direct-product isomorphism,
identifying Y/O₂(Y) with L_U/O₂(L_U) × I/O₂(I) on the original quotient
representatives. The S₃ branch has explicit
equivariant tensor coordinates on the actual B/U, with its inclusion
identified using fixedness and the source's two-copy rank identity.
The dihedral rows recover F₄ directly from the rotation, transport those
scalars to the literal B/U, and retain the canonical conjugation action and
original quotient representatives in the tensor formula. The code branch's rank-six fixed-space contradiction is proved directly
from the order-five action.

Still required: the full small-action sieve, marked scalar/tensor
recognition for the cocode SL₂(4) row, the code branch's dihedral-five
selection, and the outer involution's fixed rank and centralization. The
complete H.4/H.15/H.16 calculations and E.2.14 remain earlier-source inputs,
with final discharge owned by the parent normalizer task. No printed binary
tensor is claimed in the dimensionally impossible cocode row.
-/
