module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.Preparation
public import Theory.Representation.SL2.BinarySmallInvolution.TripleFixedSpaces

/-!
# Excluding the SL₂(8) triple tensor in K.3.1

The three-factor Frobenius tensor has fixed codimensions 4, 6, and 7 on
nontrivial elementary two-subgroups of orders 2, 4, and 8. Thus its binary
form has cubic ratio greater than two. In the actual source configuration,
the odd field degree puts every two-subgroup of the ambient actor in the
layer; `Preparation` transports the source ratio bound to the literal
SL₂ representation. Applying the intrinsic calculation excludes the triple
alternative, without an ambient-actor containment or degree-selection premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.1,
printed pp.453–454. This is the exceptional-module exclusion used in the
separate natural/Hermitian recognition assembly.
-/

@[expose] public section
open scoped MatrixGroups
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The actual SL₂(8) layer action in the source configuration cannot be the
binary form of the three-factor Frobenius tensor. -/
theorem psl2_not_isTriple_of_card_eight (h : SourceHypotheses ρ L)
    (e : L ≃* SL(2,K)) (hK : Nat.card K = 8) :
    ¬ SL2.BinarySmall.IsTriple ((ρ.comp L.subtype).comp e.symm.toMonoidHom) := by
  intro htriple
  exact SL2.BinarySmall.TripleFixedSpaces.not_cubicRatio_le_two hK _ htriple
    (h.psl2_matrix_cubicRatio_le_two_of_odd e (r := 3)
      (by simpa using hK) (by decide))

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
