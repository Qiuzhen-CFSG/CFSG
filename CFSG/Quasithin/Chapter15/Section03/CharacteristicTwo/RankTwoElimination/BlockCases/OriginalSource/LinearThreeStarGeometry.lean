module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeLarger.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# Normality of a larger linear-three star component

The actual nonnormal-component catalogue leaves binary PSL2 or PSL3(2)
as the core quotient. Neither admits a surjection onto SL3(2^n), n>1:
SL2 has elementary two-subgroups and the binary PSL3 order has too small
a two-part. The original component is therefore normal. The source actor
also normalizes R by its defining two-core, is solvable, and contains the
literal component Sylow S intersect L. No central-cover identification or
block reconstruction is needed.

Source: Aschbacher–Smith 1.2.1(3) and 15.3.11–12, 15.3.17–20,
printed pp.503,1123–1127.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

theorem linearThree_star_component_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : starImage c.L d.R c.L ≃* SL(3,F)) :
    (c.L.subgroupOf I).Normal := by
  let : Nontrivial SL(3,F) := (Finite.one_lt_card_iff_nontrivial (α := SL(3,F))).mp (by
    apply lt_of_lt_of_le _ (Nat.card_le_card_of_injective
      (Matrix.PSL3.LinearThree.unipotentSL F).subtype
      (Matrix.PSL3.LinearThree.unipotentSL F).subtype_injective)
    rw [Matrix.PSL3.LinearThree.card_unipotentSL]
    exact one_lt_pow₀ Finite.one_lt_card (by decide : 3 ≠ 0))
  by_contra hnormal
  let q := e.toMonoidHom.comp (coreToStar hR)
  have hq : Function.Surjective q := e.surjective.comp (coreToStar_surjective hR)
  rcases SourceRankOne.OriginalSource.source_component_models_of_nonnormal
    hG d hI hf c hnormal hS with ⟨m,hm,ha,_⟩ | ⟨ha,_⟩
  · obtain ⟨E,hfieldE,hfiniteE,hE,⟨a⟩⟩ := ha
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hE)
    have h4 : 3 < Nat.card E := by
      rw [hE]
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hm
      omega
    let : IsSimpleGroup PSL(2,E) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    let f := q.comp a.symm.toMonoidHom
    have hf : Function.Surjective f := hq.comp a.symm.surjective
    have hi : Function.Injective f := f.injective_of_surjective_of_simple hf
    let b := (MulEquiv.ofBijective f ⟨hi,hf⟩).symm.trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm
    exact Matrix.SpecialLinearGroup.not_injective_linearThree_to_binaryLinearTwo
      b.toMonoidHom b.injective
  · obtain ⟨E,hfieldE,hfiniteE,hE,⟨a⟩⟩ := ha
    have hcE : Nat.card PSL(3,E) = 168 := by
      simpa [hE] using Matrix.PSL3.LinearThree.card_projective_mul_scalar E
    have hc : Nat.card (c.L ⧸ pCore 2 c.L) = 168 := (Nat.card_congr a.toEquiv).trans hcE
    have hd : Nat.card SL(3,F) ∣ 168 := hc ▸ Subgroup.card_dvd_of_surjective q hq
    have h4 : 4 ∣ Nat.card F := by
      rw [hF]
      exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ n)
    have h64 : 64 ∣ Nat.card (Matrix.PSL3.LinearThree.unipotentSL F) := by
      rw [Matrix.PSL3.LinearThree.card_unipotentSL]
      exact pow_dvd_pow_of_dvd h4 3
    have ht := h64.trans ((Matrix.PSL3.LinearThree.unipotentSL F).card_subgroup_dvd_card.trans hd)
    exact (by decide : ¬64 ∣ 168) ht

/-- The original hypotheses give both normalizers, solvability, and the
literal component Sylow needed for the natural star action. -/
theorem linearThree_star_source_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : starImage c.L d.R c.L ≃* SL(3,F)) :
    d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G) ∧
      d.Yplus ⊔ d.S ≤ normalizer (d.R : Set G) ∧
      Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) ∧
      ∃ P : Sylow 2 c.L, (P : Subgroup c.L) = d.S.subgroupOf c.L := by
  have hS := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  have h := RankTwoElimination.OriginalSource.rankTwo_component_input_from_case
    hG d hempty hM hu hmany hI htwo hf c
  have hnL := linearThree_star_component_normal hG d hI hf c hS h.normalizes hF hn e
  have hnR : d.Yplus ⊔ d.S ≤ normalizer (d.R : Set G) :=
    (d.Yplus ⊔ d.S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  refine ⟨hI.1.2.trans ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnL),
    hnR, LinearThreeLarger.local_solvable d htwo, ?_⟩
  obtain ⟨S,hS⟩ := hS
  exact LinearThree.Extension.SourceCases.component_sylow d c S hS
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
