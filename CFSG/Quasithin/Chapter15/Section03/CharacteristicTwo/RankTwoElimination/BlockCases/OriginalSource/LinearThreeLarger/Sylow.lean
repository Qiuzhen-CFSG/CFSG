module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.NonnormalModels
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.SelectedSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.SourceQuotients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SL2.NoLinearThreeEmbedding
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.GroupTheory.SolvableNormalSup

/-!
# The original larger SL₃ block and its local actor

The original nonnormal-component theorem compares the actual local C-component
with its faithful Thompson action. A nonnormal component has binary PSL₂ or
PSL₃(2) core quotient. Neither can be SL₃(2ⁿ) for n > 1: its unitriangular
group contains an element of order four, excluding binary PSL₂, and has order
divisible by 64, excluding PSL₃(2). Thus the component is normal in I.

The original cubic quotient makes Y₊ solvable; S normalizes Y₊, so Y₊S is
solvable. The final theorem supplies this actual actor's normalization and
marks the component Sylow as S ∩ L. These are the source inputs for the two
invariant parabolics in the larger linear-three exclusion.

Source: Aschbacher–Smith, 1.2.1(3), B.5.6, and 15.3.11–12, 15.3.20,
printed pp.503, 105, 1123–1127. The nonnormal comparison is also used in
15.3.27, printed p.1130, and needs no rank-one assumption on Y₊.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterA.Section05To06
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeLarger
variable {G : Type*} [Group G] [Finite G]

/-- The full local actor is solvable in the original cubic-quotient case. -/
theorem local_solvable (d : LocalData G) {I : Subgroup G}
    (htwo : OutsideStructure.RankTwoCase d I) :
    Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq := (ComponentIntersection.cubic_quotient_facts d.Yplus htwo.1).1
  let := (pCore_isPGroup (p := 2) (G := d.Yplus)).isNilpotent
  let := hq.isNilpotent
  let : Group.IsSolvable d.Yplus :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 d.Yplus)).mpr
      ⟨inferInstance, inferInstance⟩
  let := (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).isNilpotent
  let H := d.Yplus ⊔ d.S
  let : (d.Yplus.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le d.Yplus.le_normalizer
      (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice))
  let : Group.IsSolvable (d.Yplus.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show d.Yplus ≤ H from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show d.Yplus ≤ H from le_sup_left)).injective
  let : Group.IsSolvable (d.S.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show d.S ≤ H from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show d.S ≤ H from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top _ _ (codisjoint_subgroupOf_sup d.Yplus d.S).eq_top

/-- The actual nonnormal-component catalogue excludes a larger natural SL₃ quotient. -/
theorem component_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hS : Chapter1.IsSylowIn 2 d.S I)
    {n : ℕ} (hn : 1 < n) (hb : ChapterC.IsSL3EvenBlock c.L n) :
    (c.L.subgroupOf I).Normal := by
  by_contra hnormal
  obtain ⟨_, _, F, hfield, hfinite, hF, hm⟩ := hb
  obtain ⟨e⟩ := hm.quotient_iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rcases SourceRankOne.OriginalSource.source_component_models_of_nonnormal
    hG d hI hf c hnormal hS with ⟨m, _, hm, _⟩ | ⟨hm, _⟩
  · obtain ⟨E, hfieldE, hfiniteE, hE, ⟨a⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hE)
    let b := (e.symm.trans a).trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm
    exact Matrix.SpecialLinearGroup.not_injective_linearThree_to_binaryLinearTwo
      b.toMonoidHom b.injective
  · obtain ⟨E, hfieldE, hfiniteE, hE, ⟨a⟩⟩ := hm
    have hcE : Nat.card PSL(3,E) = 168 := by
      simpa [hE] using Matrix.PSL3.LinearThree.card_projective_mul_scalar E
    have hcF : Nat.card SL(3,F) = 168 :=
      (Nat.card_congr (e.symm.trans a).toEquiv).trans hcE
    have h4 : 4 ∣ Nat.card F := by
      rw [hF]
      exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ n)
    have h64 : 64 ∣ Nat.card (Matrix.PSL3.LinearThree.unipotentSL F) := by
      rw [Matrix.PSL3.LinearThree.card_unipotentSL]
      exact pow_dvd_pow_of_dvd h4 3
    have hd := h64.trans (Matrix.PSL3.LinearThree.unipotentSL F).card_subgroup_dvd_card
    rw [hcF] at hd
    exact (by decide : ¬ 64 ∣ 168) hd

/-- Original selection supplies the full actor's normalization and the literal
component Sylow marking used in the two invariant parabolics. -/
theorem source_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    {n : ℕ} (hn : 1 < n) (hb : ChapterC.IsSL3EvenBlock c.L n) :
    d.Yplus ⊔ d.S ≤ normalizer (c.L : Set G) ∧
      Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) ∧
      ∃ P : Sylow 2 c.L, (P : Subgroup c.L) = d.S.subgroupOf c.L := by
  have hS := (OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I hI).sylow
  have hnL := component_normal hG d hI hf c hS hn hb
  refine ⟨hI.1.2.trans ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnL),
    local_solvable d htwo, ?_⟩
  obtain ⟨S, hS⟩ := hS
  exact LinearThree.Extension.SourceCases.component_sylow d c S hS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.LinearThreeLarger
