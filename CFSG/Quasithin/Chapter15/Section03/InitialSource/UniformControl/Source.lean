module
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.SeedSource
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Restriction
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selection
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.AlternatingThree.Complete
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Source

/-!
# Original14.1.11 and the selected maximum in14.1.12

One universal characteristic pair is chosen on the original Baumann subgroup.
In every noncentral local group, the seed centralizer is C_M(V)T. Failure
of the original normalizer factorization would therefore make the control
of the SAME restricted pair proper. Fixed-pair C.1.28 for the solvable
canonical action constructs a moving A₃ block, contradicted by14.1.10.
The centralizing case is the existing Baumann Frattini argument.

The actual normalizer choice then gives the ordering maximum, its uniqueness,
its distinction from Mc and the original relative-normalizer and centralizer
bounds. No local factorization, block, action-coordinate or source A/C
callback remains. Source: Aschbacher--Smith14.1.11--12, pp.978--979.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
open ChapterB ChapterC.GlaubermanNiles ChapterA.Section05To06
open ChapterC.RankOne.ChiProduct.FixedPairSolvable
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full characteristic-normalizer factorization in the original local group. -/
theorem source_characteristic_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u}) :
    M = (M ⊓ centralizer (localModule T M : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) := by
  let : D.second.Characteristic := D.second_characteristic
  by_cases hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)
  · exact source_centralizing_factorization hG T hM hJ D.second
  let hH : M ∈ Chapter1.HOver G (T : Set G) := ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1,hM.2⟩
  let U := (localModule T M).subgroupOf M
  let := (localModule_reduced_from_source hG T hH).normal
  let := (localModule_reduced_from_source hG T hH).elementary
  by_contra hfail
  let S := T.subtype hM.2
  let DM := subtypePair T D M hM.2
  have hproper : control S DM ≠ ⊤ := by
    intro ht
    apply hfail
    apply le_antisymm
    · have hm := subtypePair_control_map_le_relative T D M hM.2
      rw [show control (T.subtype hM.2) (subtypePair T D M hM.2) = ⊤ from ht,
        ←MonoidHom.range_eq_map,range_subtype] at hm
      exact hm.trans (sup_le
        (source_noncentral_seed_le_characteristic_supplement hG T hempty hM hu hcase hJ D)
        le_sup_right)
    · exact sup_le inf_le_left inf_le_left
  let ec := QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun W : Subgroup M => centralizer (W : Set M))
      (omegaClosure_eq_localModule T M hM.2))
  have hs : Group.IsSolvable (M ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup M) : Set M) : Set M)) := by
    let : Group.IsSolvable (M ⧸ centralizer (U : Set M)) := reduced_action_isSolvable
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      hG T hempty hH U (localModule_reduced_from_source hG T hH)
    exact Group.isSolvable_of_isSolvable_injective (f := ec.toMonoidHom) ec.injective
  obtain ⟨X,hb,hx,hm,_,_⟩ := exists_moving_alternatingThree_of_fixed_pair_escape S
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mpr (hG.evenCharacteristic T M hM.1 hM.2))
    DM (subtypePair_universal T D hD M hM.2) hproper
    ((hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)) hs
  exact alternating_three_excluded_from_source hG T hM hu hmany X (S : Subgroup M) hb
    (pCore_isPGroup.le_sylow_of_normal S) le_rfl hm hcase hx


/-- Original14.1.11, including its literal set-product conclusion. -/
theorem source_lemma_14_1_11
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ C : Subgroup (baumann (T : Subgroup G)), C.Characteristic ∧ C ≠ ⊥ ∧
      ∀ M ∈ maximalTwoLocalOvergroups (T : Subgroup G),
        (M : Set G) = (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) *
            (M ⊓ normalizer (C.map (baumann (T : Subgroup G)).subtype : Set G) : Subgroup G) ∨
          (M = Mc ∧ 2 < Nat.card (centralInvolutions T)) := by
  obtain ⟨D,hD,_⟩ := ChapterC.RankOne.ChiProduct.FixedPair.exists_uniform_pair.{u,u}
    T (MainForward.sylow_ne_bot hG T)
  refine ⟨D.second,D.second_characteristic,D.second_ne_bot,?_⟩
  intro M hM
  by_cases hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2
  · have hf := source_characteristic_factorization hG T hempty hM hu hmany hcase D hD
    have hn : M ≤ normalizer (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) :=
      (le_inf M.le_normalizer ((le_normalizer_conjugateSpanBy (centralInvolutions T) M).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
    exact Or.inl ((congrArg (fun H : Subgroup G => (H : Set G)) hf).trans
      (coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hn)))
  · have he : M = Mc := by
      by_contra hne
      exact hcase (Or.inl hne)
    have hc : Nat.card (centralInvolutions T) ≠ 2 := fun h => hcase (Or.inr h)
    have hz : centralInvolutions T ≠ ⊥ := by
      intro hz
      apply ChapterC.RankOne.ChiProduct.FixedPair.firstSeed_ne_bot T D
      exact bot_unique ((show ChapterC.RankOne.ChiProduct.FixedPair.firstSeed T D ≤
        centralInvolutions T from inf_le_left).trans_eq hz)
    have hp := (centralInvolutions T).one_lt_card_iff_ne_bot.mpr hz
    exact Or.inr ⟨he,by omega⟩

/-- The original14.1.12 maximum is selected from the normalizer of the SAME
source pair, with its full ordering, normalizer and centralizer conclusions. -/
theorem source_lemma_14_1_12_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ∃ D : CharacteristicPair (baumann (T : Subgroup G)), D.Universal.{u,u} ∧
      ∃ Mf : Subgroup G,
        Mf ∈ maximalTwoLocalOvergroups
          (normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
        Mf ≠ Mc ∧ IsOrderingMaximal T Mf ∧
        normalizer (baumann (T : Subgroup G) : Set G) ≤ Mf ∧
        (∀ M ∈ maximalLocals T, M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2 →
          OrderingLE T M Mf) ∧
        (∀ M ∈ maximalLocals T, M ≠ Mc →
          (∀ N ∈ maximalLocals T, N ≠ Mc → OrderingLE T M N → N = M) → M = Mf) ∧
        (Nat.card (centralInvolutions T) = 2 → ∀ M, IsOrderingMaximal T M → M = Mf) ∧
        (∀ Vf : Subgroup G, localModule T Mf ≤ Vf → Vf ≤ Mf → (Vf.subgroupOf Mf).Normal →
          maximalTwoLocalOvergroups
            (Mf ⊓ normalizer ((T : Subgroup G) ⊓ centralizer (Vf : Set G) : Subgroup G)) = {Mf} ∧
          ∀ M ∈ maximalLocals T, Mf ⊓ centralizer (Vf : Set G) ≤ M) := by
  obtain ⟨D,hD,_⟩ := ChapterC.RankOne.ChiProduct.FixedPair.exists_uniform_pair.{u,u}
    T (MainForward.sylow_ne_bot hG T)
  let : D.second.Characteristic := D.second_characteristic
  obtain ⟨Mf,hMf,hne,hmax,hdom,hoff,hall,hC⟩ := source_normalizer_selection_of_factorization
    hG T hu hmany D.second D.second_ne_bot
    (fun M hM hcase => source_characteristic_factorization hG T hempty hM hu hmany hcase D hD)
  refine ⟨D,hD,Mf,hMf,hne,hmax,
    (normalizer_le_normalizer_characteristic_image _ D.second).trans hMf.2,
    hdom,hoff,hall,?_⟩
  intro Vf hVV hVM hn
  let : (Vf.subgroupOf Mf).Normal := hn
  exact ⟨source_unique_overgroup_sylow_centralizer hG T hmax Vf hVV hVM,
    fun M hM => (inf_le_inf_left Mf (centralizer_le hVV)).trans (hC M hM)⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl
