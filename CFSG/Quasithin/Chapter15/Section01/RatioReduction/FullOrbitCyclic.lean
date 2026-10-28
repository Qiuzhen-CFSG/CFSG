module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ClassifiedNoThree
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TransitiveFactors

/-!
# Cyclic starred actors in the decomposable full-orbit branch

A noncyclic starred factor has an elementary three-core of rank two or
three and a marked moving involution. The original SQTK rank bound makes
its embedded actor normal. This is incompatible with a nonsingleton
transitive family, so every factor has the genuine cyclic D.2.17 source
witness, on its original action and carrier.

Source: Aschbacher--Smith 15.1.2, printed pp.1084 and 1086.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition ChapterD.FittingConfigurations
variable {G : Type*} [Group G] [Finite G]

/-- Noncyclic starred factors are ambient normal, directly from their marked
three-core and the original rank-two cover. -/
theorem source_localAction_factor_normal_of_noncyclic_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index) (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action → ¬ IsCyclic A →
      (c.ambientFactor d i).actor.Normal := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i A hA hncyc
  have hr : 1 < rank A := by
    have hp := hA.1.2.1.rank_pos
    by_contra hn
    have hr : rank A = 1 := by omega
    have hc : Nat.card A = 2 := by rw [hA.1.2.1.card_eq_two_pow_rank,hr]; norm_num
    exact hncyc (isCyclic_of_prime_card hc)
  let F := d.factor i
  let j : F.Carrier →* D := (Jhat ρ).subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) ((Jhat ρ).subtype_injective.comp F.embedding.group_injective)
  obtain ⟨B,r,hB,hrB⟩ := c.factor_cover d
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i
  obtain ⟨s,h,ds,_,_⟩ := SourceReduction.source_noncyclic_global_configurations F.action
    hB r hrB F.faithful hA hr (generalizedFitting_eq_fitting_of_solvable F.Carrier)
    (c.factor_twoCore d (source_localAction_twoCore hG T hM) i) (hd i) F.generated
  let : IsElementaryAbelian 3 (pCore 3 F.Carrier) := h.elementary
  have hn : ¬ IsCyclic (pCore 3 F.Carrier) := by
    intro hc
    let := hc
    have hh := IsElementaryAbelian.exponent_dvd_p 3 (pCore 3 F.Carrier)
    rw [IsCyclic.exponent_eq_card,h.card_core] at hh
    rcases h.rank_cases with hs | hs <;> rw [hs] at hh <;> norm_num at hh
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr h.starred.1.2.1.1
  obtain ⟨a,ha⟩ := exists_ne (1 : A)
  have ha1 : (a : F.Carrier) ≠ 1 := fun he => ha (Subtype.ext he)
  have ha2 : orderOf (a : F.Carrier) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (a : F.Carrier) a.property) ha1
  have ham : (a : F.Carrier) ∉ centralizer (pCore 3 F.Carrier : Set _) := by
    intro hh
    have hm : (a : F.Carrier) ∈ A ⊓ centralizer (pCore 3 F.Carrier : Set _) := ⟨a.property,hh⟩
    rw [h.actor_faithful] at hm
    exact ha1 hm
  exact source_localAction_factor_actor_normal hG T hempty hM hmany hJ U c d hd
    3 (by decide) i hn a ha2 ham
theorem source_localAction_transitive_factor_cyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      ∀ i, ∀ A ∈ QhatStar (d.factor i).action, IsCyclic A := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd π hp ht hmore i A hA
  by_contra hn
  exact c.transitive_actor_not_normal d π hp ht hmore i
    (source_localAction_factor_normal_of_noncyclic_star hG T hempty hM hmany hJ U c d hd i A hA hn)

theorem source_localAction_transitive_factor_localGeneration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive (localModule T M)))
      (c : FactorData ρ (Jhat ρ) U) (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ i j, ∃ g : D, π g i = j) → 1 < Nat.card d.Index →
      ∀ i, Nonempty (CyclicSource.LocalGeneration (d.factor i).action) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd π hp ht hmore i
  exact c.factor_cyclic_localGeneration d (source_localAction_twoCore hG T hM)
    (source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ) hd
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i
    (source_localAction_transitive_factor_cyclic hG T hempty hM hmany hJ U c d hd π hp ht hmore i)
end CFSG.Quasithin.Chapter15.Section01
