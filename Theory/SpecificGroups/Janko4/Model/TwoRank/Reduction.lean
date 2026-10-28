module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.FixedBound
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Two-rank reduction for the actual J₄ max1 action

An elementary subgroup of a local Sylow group maps into the already certified
Mathieu quotient Sylow group. Its intersection with the elementary kernel
embeds into the fixed masks of that image. Thus the finite action inequality
`|B| |FixedMasks B| ≤ 2048` bounds every elementary subgroup by 2¹¹.
The existing ambient Sylow inside max1 then gives the intrinsic J₄ rank bound.
Full innerness identifies the automorphism group once the inherited simple
and perfect hypotheses make the center trivial.

The finite inequality is an explicit outstanding premise of this reduction;
none of the declarations below asserts that it has been checked. The quotient
maps and the direct (not dual) action retain the existing eleven basis pairs.

Source: Aschbacher–Smith, G.7.3(2), printed pp.347–348, citing Asc82a and
GLS98 5.2.10/5.6.1. Local words and coordinate provenance are documented in
`Cardinality.Subgroup` and `LocalStructure.Mathieu.SylowCore.Transport`.
-/

@[expose] public section
namespace Janko4.TwoRank
set_option backward.isDefEq.respectTransparency true
open Subgroup LocalStructure LocalStructure.SylowCore
open LocalStructure.SylowCore.Transport
open Simplicity.Max1Fusion.QuotientInvolutions
open Theory.GroupTheory
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel
  Cardinality.max1Subgroup

/-- The exact aligned quotient and kernel centralizer give the elementary order bound. -/
theorem sylow_elementary_card_le_of_fixedBound (h : ElementaryFixedBound) (P : Sylow 2 Local)
    (A : Subgroup P) [IsElementaryAbelian 2 A] : Nat.card A ≤ 2 ^ 11 := by
  obtain ⟨g, hg⟩ := exists_alignment P
  let f := alignedHom P g hg
  have hB : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hc := h (A.map f) hB
  have hk := centralizer_card_le_fixedMasks P A g hg
  have hA := card_le_image_mul_centralizer (core P) A
  rw [← alignedHom_image_card P g hg A] at hA
  exact hA.trans ((Nat.mul_le_mul_left _ hk).trans hc)

/-- The repository prime-rank convention is reduced to elementary subgroup orders. -/
theorem local_twoRank_le_eleven_of_fixedBound (h : ElementaryFixedBound) : primeRank 2 Local ≤ 11 := by
  let P : Sylow 2 Local := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro A hA
  let := hA
  exact sylow_elementary_card_le_of_fixedBound h P A

/-- Restriction to the existing ambient Sylow transfers the bound to J₄. -/
theorem model_twoRank_le_eleven_of_fixedBound (h : ElementaryFixedBound) : primeRank 2 Model ≤ 11 := by
  rw [AdequateLocal.ambientSylow.primeRank_eq]
  let f := Subgroup.inclusion AdequateLocal.ambientSylow_le_M
  exact (primeRank_le_of_injective 2 f
    (Subgroup.inclusion_injective _)).trans (local_twoRank_le_eleven_of_fixedBound h)

/-- Full innerness transfers the intrinsic bound to all automorphisms. -/
theorem automorphism_twoRank_le_eleven_of_fixedBound
    [IsSimpleGroup Model] [Group.IsPerfect Model] (h : ElementaryFixedBound) :
    primeRank 2 (MulAut Model) ≤ 11 := by
  let e : Model ≃* MulAut Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect,
      AdequateLocal.conj_surjective⟩
  rw [← primeRank_equiv 2 e]
  exact model_twoRank_le_eleven_of_fixedBound h

end Janko4.TwoRank
