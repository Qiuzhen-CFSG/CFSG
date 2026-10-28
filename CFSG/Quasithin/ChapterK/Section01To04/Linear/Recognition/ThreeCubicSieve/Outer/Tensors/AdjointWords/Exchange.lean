module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Paired

/-!
# Adjoint-word exchange from paired component coordinates

The existing paired-component comparison applies to any Schur-linear
involution with an actual involutory lift to SL₃. It does not require a
natural factor or a companion in an elementary actor. Interchange and the
original operator induce the same component automorphism, and absolute
Schur rigidity removes their scalar ratio in characteristic two.

Here that comparison constructs the exchange model consumed by the adjoint
quarter-displacement bound. The existence of paired component coordinates
for field-containing automorphisms remains a geometric obligation. No
natural-word realization premise is used.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2,4,5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]
    {t : linearNormalizer σ}

/-- Recover the literal exchange operator from the component coordinates.
The lift and the equivalence are on the actual cover and original Schur module. -/
def exchangeRealization_of_pairedCoordinates
    (L : Realization.LiftedInvolution B σ t) (ht : IsSchurLinear σ t)
    (P : Realization.PairedTensorCoordinates B σ L.automorphism) :
    ExchangeRealization B σ t ht where
  size := P.size
  two_le := by have := P.three_le; omega
  equiv := P.equiv
  action := P.outer_action L ht

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
