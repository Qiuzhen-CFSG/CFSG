module
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import CFSG.Quasithin.Chapter10.SourceA5HallGeneration
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport

/-!
# Numerical reduction on the original full Chapter 10 module

A nontrivial perfect action on an elementary abelian two-group has moved
subgroup of order at least eight: on a smaller two-group its permutation
image would be both perfect and solvable. This applies to the actual
commutator [V_M,L] without an A5 or SL3 marking and without ambient normality
of L. Point-centralizer control therefore gives r≥3.

The original kernel uniqueness and attained generation theorem then give
w≤n(H) whenever n(H)≤2. The multiple-overgroup guard supplies an actual H*,
so w≤2 and the minimum is attained by the literal V_M^g∩M. If the independent
small-offender argument proves w≥2, all generation parameters equal two.
These results supply the numerical part of the survivor assembly; point
control, the generation cap and small-offender recognition remain inputs.

Source: Aschbacher--Smith 10.2.9(2), 10.2.12--13 and E.3.35,
combined manuscript of 1 March 2004, printed pp.750,754--755 and238.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- Every original full moved factor has at least eight elements. -/
theorem source_full_moved_card_ge_eight : 8 ≤ Nat.card (⁅D.fullModule,L⁆ : Subgroup G) := by
  classical
  let W := ⁅D.fullModule,L⁆
  let := D.fullModule_elementary (uniqueness D)
  let := Chapter1.mem_L_isPerfect D.maximal.1
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp hLV
  have hW : IsPGroup 2 W := (IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hWV
  by_contra hnot
  obtain ⟨n,hn⟩ := hW.exists_card_eq
  have hnlt : n < 3 := by
    by_contra hnge
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hnge)
    rw [← hn] at hh
    exact hnot hh
  have hsmall : Nat.card W ≤ 4 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2)
  let : Fintype W := Fintype.ofFinite W
  have hc : Fintype.card W ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hsmall
  let e : W ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm W) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  let f : L →* Equiv.Perm W := (MulAction.toPermHom (MulAut W) W).comp
    (W.normalizerMonoidHom.comp (inclusion hLW))
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hLC : L ≤ centralizer (W : Set G) := by
    intro l hl w hw
    have hf : f ⟨l, hl⟩ = 1 := congrArg Subtype.val
      (Subsingleton.elim (f.rangeRestrict ⟨l, hl⟩) 1)
    have he := congrArg (fun a : Equiv.Perm W => (a ⟨w, hw⟩ : G)) hf
    change l * w * l⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact source_full_moved_ne_bot D
    (commutator_eq_bot_of_iterated_eq_bot D.fullModule L
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hLC)))

/-- Source point-centralizer control forces r≥3 without a module model. -/
theorem source_fullModule_globalR_three_of_element_centralizers
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal) :
    (3 : ℕ∞) ≤ globalR D.fullModule := by
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hr := source_fullModule_globalR_lower_of_element_centralizers D
    (le_normalizer_iff_commutator_le_left.mp hLV) hcent
  have hlog : 3 ≤ Nat.log 2 (Nat.card (⁅D.fullModule,L⁆ : Subgroup G)) := by
    have hh := Nat.log_mono_right (b := 2) (source_full_moved_card_ge_eight D)
    norm_num at hh
    exact hh
  exact le_trans (by exact_mod_cast hlog) hr

/-- The original H* generation comparison, with its positivity premise discharged. -/
theorem source_fullModule_globalW_le_generation_of_element_centralizers
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hbound : generationParameter H ≤ 2) :
    globalW D.fullModule (T : Subgroup G) ≤ (generationParameter H : ℕ∞) := by
  have hr := source_fullModule_globalR_three_of_element_centralizers D hcent
  have hn : (generationParameter H : ℕ∞) < globalR D.fullModule :=
    (lt_of_le_of_lt (by exact_mod_cast hbound) (by decide : (2 : ℕ∞) < 3)).trans_le hr
  exact (min_le_iff.mp (source_overgroup_generation_bound D hH.1.1.2 hH.1.2
    (source_hstar_generation_positive D hH))).resolve_right (not_le_of_gt hn)

/-- The genuine standing guard supplies an H*, so its generation cap bounds w. -/
theorem source_fullModule_globalW_le_two_of_generation_bound
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hbound : ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      generationParameter H ≤ 2) : globalW D.fullModule (T : Subgroup G) ≤ 2 := by
  have hout := Chapter3.hasMaximalOutside_of_many T hmany D.maximalLocal
    (uniqueness D).normalizer_maximal (le_normalizer_componentOrbit L T)
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact (source_fullModule_globalW_le_generation_of_element_centralizers D hcent hH
    (hbound H hH)).trans (by exact_mod_cast hbound H hH)

/-- The exact original offender attaining w, with the same full module and
maximal normalizer; no A5 quotient or Hall-placement premise is required. -/
theorem source_fullModule_small_offender
    (hw : globalW D.fullModule (T : Subgroup G) ≤ 2) :
    ∃ g ∉ D.maximalLocal,
      ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      globalW D.fullModule (T : Subgroup G) =
        (subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
          (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) : ℕ∞) ∧
      subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
        (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2 := by
  let := D.fullModule_elementary (uniqueness D)
  obtain ⟨g,hg⟩ := exists_isWOffenderAt_of_globalW_ne_top
    (source_fullModule_weakClosure_hypotheses D) (ne_top_of_le_ne_top (by simp) hw)
  have he := hg.2
  unfold offenderNormalizer at he
  rw [source_fullModule_normalizer D] at he
  refine ⟨g,?_,hg.1,he,by exact_mod_cast (he ▸ hw)⟩
  intro hgm
  apply hg.1
  have heq : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hgm)
  rw [heq]
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer _)

/-- The reverse weak-closure bound forces both equalities in source10.2.13,
including the generation parameter of every actual H*. -/
theorem source_fullModule_parameters_eq_two_of_lower_bound
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcent : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
      centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hbound : ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      generationParameter H ≤ 2)
    (hwl : 2 ≤ globalW D.fullModule (T : Subgroup G)) :
    globalW D.fullModule (T : Subgroup G) = 2 ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal, generationParameter H = 2 := by
  have hw := le_antisymm
    (source_fullModule_globalW_le_two_of_generation_bound D hmany hcent hbound) hwl
  refine ⟨hw,fun H hH => le_antisymm (hbound H hH) ?_⟩
  have hg := source_fullModule_globalW_le_generation_of_element_centralizers D hcent hH
    (hbound H hH)
  rw [hw] at hg
  exact_mod_cast hg

end CFSG.Quasithin.Chapter10
