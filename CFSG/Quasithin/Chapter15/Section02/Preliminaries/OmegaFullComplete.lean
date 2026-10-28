module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullStructure
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaCentralizerRank

/-!
# Complete original15.2.3 in the Omega row

The cubic and order-nine proofs give all three residual alternatives on the
same original Y, Rc, chosen module and quotient maps. This module assembles
them with normality, factorization, uniqueness and star centralization.
The common three-rank bound on C_M(V) excludes the elementary-nine star
image of O²(H∩M) that occurs at the start of15.2.4; the original prepared
module supplies its centralizer placement.

The general chosen-module assembly retains only the preceding intersection-
core noncentrality assertion. For V=V(M), the original core-growth producer
discharges it, giving the complete full-module theorem. The proper-module
producer is developed independently and can feed the same assembly.

Source: Aschbacher--Smith15.2.3 and the first paragraph of15.2.4,
printed pp.1104--1106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The three complete source alternatives, using the original action and star images. -/
def OmegaResidualAlternatives (T : Sylow 2 G) (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) : Prop :=
  let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
  let f := (actionHom M V hn).rangeRestrict
  let Ybar := (Y.subgroupOf M).map f
  let P := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
  let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
  let C := M ⊓ centralizer (V : Set G)
  (Ybar = pResidual 2 (actionHom M V hn).range ∧ Nonempty (Ybar ≃* P) ∧
      Nat.card P = 9 ∧ Nonempty (P ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) ∧
      Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∧ Nat.Coprime 3 (Nat.card C)) ∨
    (Ybar = pResidual 2 (actionHom M V hn).range ∧
      Nat.card P = 27 ∧ IsExtraspecial 3 P ∧ Nonempty (P ≃* HeisenbergPrime 3) ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧ Nat.card R = 2 ∧
      (∀ r ∈ R, r ≠ 1 → ∀ y ∈ Ybar, r * y * r⁻¹ = y⁻¹) ∧
      (centralPreimage (pCore 2 Y)).map Y.subtype = Y ⊓ centralizer (V : Set G) ∧
      twoResidualAmbient ((centralPreimage (pCore 2 Y)).map Y.subtype) = theta C) ∨
    (Nat.card Ybar = 3 ∧ Nonempty (Ybar ≃* Multiplicative (ZMod 3)) ∧
      Nat.card P = 3 ∧ Nonempty (P ≃* Multiplicative (ZMod 3)) ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* Multiplicative (ZMod 3)) ∧
      Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∧ Nat.card R = 2 ∧
      (∀ r ∈ R, r ≠ 1 → ∀ y ∈ Ybar, r * y * r⁻¹ = y⁻¹) ∧
      ∀ S : Sylow 3 M, ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (S ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n))))

/-- All five clauses of15.2.3 in the Omega row, plus its common centralizer-rank bound. -/
structure OmegaResidualConclusions (T : Sylow 2 G) (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) : Prop where
  image_nontrivial :
    ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).map
      (actionHom M V hn).rangeRestrict ≠ ⊥
  image_movement :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
    let f := (actionHom M V hn).rangeRestrict
    ⁅(Y.subgroupOf M).map f, (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f⁆ =
      (Y.subgroupOf M).map f
  alternatives : OmegaResidualAlternatives T M Mc V hn
  normal : ((caseIIResidual T M (chosenStarredPreimage M V hn) Mc).subgroupOf M).Normal
  unique_of_full_image :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
    (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict =
        pResidual 2 (actionHom M V hn).range →
      maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M}
  factorization : (M : Set G) = ((M ⊓ Mc : Subgroup G) : Set G) *
    (twoResidualAmbient (chosenStarredPreimage M V hn) : Set G)
  star_centralizes :
    let q := QuotientGroup.mk' (pCore 2 M)
    let Y := caseIIResidual T M (chosenStarredPreimage M V hn) Mc
    (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map q ⊔ (Y.subgroupOf M).map q ≤
      centralizer (((M ⊓ centralizer (V : Set G)).subgroupOf M).map q : Set (M ⧸ pCore 2 M))
  centralizer_rank : primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1

/-- The complete chosen-module Omega assembly; the preceding source noncentrality
is the sole retained branch-producing input. -/
theorem source_omega_residual_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    OmegaResidualConclusions T M Mc V hV.normalized := by
  obtain ⟨hne, hmove, hbranches⟩ := source_omega_residual_structure hG T hempty hM hJ hu hV ho hRc
  refine ⟨hne, hmove, ?_, source_omega_lemma_15_2_3_2 T hM.1.2 hV.normalized ho,
    source_omega_lemma_15_2_3_3_of_residual_image hG T hempty hM hJ hV ho,
    source_omega_lemma_15_2_3_4 T hM.1.2 hu hV.normalized ho,
    source_omega_lemma_15_2_3_5 T hM.1.2 hu hV ho,
    source_omega_centralizer_rank hG T hM.1 hu hV ho hRc⟩
  rcases hbranches with ⟨hc, hker, hs, hR, hinv⟩ | ⟨hn, _⟩
  · let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let P := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    let e : P ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hs (by simp)
    exact Or.inr (Or.inr ⟨hc, ⟨mulEquivOfPrimeCardEq hc (by simp)⟩, hs, ⟨e⟩,
      ⟨(omegaResidualCoreQuotientEquivStar T hM.1.2 hV.normalized ho).trans e⟩,
      hker, hR, hinv, (source_omega_cubic_sylow_structure hG T hM.1 hu hV ho hc).2⟩)
  · obtain ⟨hfull, he | hx⟩ := source_omega_nine_residual_structure hG T hM.1 hu hV ho hn
    · rcases he with ⟨hc, ⟨eP⟩, hq, hker, hcop⟩
      obtain ⟨eA⟩ := SymmetricThreeProductResidual.residual_equiv_elementaryNine ho.2.2.2.1.some
      exact Or.inl ⟨hfull, ⟨((MulEquiv.subgroupCongr hfull).trans eA).trans eP.symm⟩,
        hc, ⟨eP⟩, hq, hker, hcop⟩
    · rcases hx with ⟨hc, hex, he, hq, hR, hinv, _, hz, ht⟩
      exact Or.inr (Or.inl ⟨hfull, hc, hex, he, hq, hR, hinv, hz, ht⟩)

/-- Complete original15.2.3 for V=V(M), with source noncentrality discharged. -/
theorem source_omega_full_residual_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M (localModule T M))
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M) hV.normalized)) :
    OmegaResidualConclusions T M Mc (localModule T M) hV.normalized :=
  source_omega_residual_complete hG T hempty hM hJ hu hV ho
    (source_omega_full_core_noncentral hG T hempty hM hu hmany ho)

end CFSG.Quasithin.Chapter15.Section02
end
