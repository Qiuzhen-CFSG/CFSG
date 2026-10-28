module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# The inner core quotient in the L₄ offender argument

Conjugation by LR on L/O₂(L), when inner, gives a surjection onto that
literal quotient. Its kernel is O₂(LR), by the centerless core-action
lemma. Two-reducedness of W_L makes this core centralize W_L, while
normal elementarity and O₂(LR) ≤ R place W_L, hence U_L, inside R.

The premises are the precise earlier conclusions of 15.3.12 and 15.3.16
and the inner-action conclusion of the first paragraph of 15.3.24.
No offender or module-classification hypothesis is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.11
and 15.3.12,16,24, printed pp.77 and 1124–1129.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders
variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
variable (hn : d.R ≤ normalizer (L : Set G))
  (hc : center (L ⧸ pCore 2 L) = ⊥)
  (hi : ∀ g : (L ⊔ d.R : Subgroup G),
    pCoreJoinAction 2 hn g ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L))

/-- Inner conjugation identifies the actual core actor, with its marking fixed by L. -/
noncomputable def coreMap : (L ⊔ d.R : Subgroup G) →* (L ⧸ pCore 2 L) :=
  (MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hc)).symm.toMonoidHom.comp
    ((pCoreJoinAction 2 hn).codRestrict _ hi)

/-- The new map retains the original conjugation action on L/O₂(L). -/
theorem coreMap_spec (g : (L ⊔ d.R : Subgroup G)) :
    MulAut.conj (coreMap d L hn hc hi g) = pCoreJoinAction 2 hn g := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hc)).apply_symm_apply
      ⟨pCoreJoinAction 2 hn g, hi g⟩)

/-- Restriction to L is the literal quotient projection. -/
theorem coreMap_on_component (l : L) :
    coreMap d L hn hc hi (inclusion le_sup_left l) = QuotientGroup.mk' (pCore 2 L) l := by
  apply Theory.GroupTheory.conj_injective_of_center_eq_bot hc
  rw [coreMap_spec, pCoreJoinAction_on_component]

/-- Every element of the core quotient comes from L itself. -/
theorem coreMap_surjective : Function.Surjective (coreMap d L hn hc hi) := by
  intro x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  exact ⟨inclusion le_sup_left l, coreMap_on_component d L hn hc hi l⟩

/-- The map has exactly the intrinsic two-core of LR as kernel. -/
theorem coreMap_ker :
    (coreMap d L hn hc hi).ker = pCore 2 (L ⊔ d.R : Subgroup G) := by
  rw [← pCoreJoinAction_kernel 2 hn (isPGroup_pCoreIn 2 _) hc]
  ext g
  change coreMap d L hn hc hi g = 1 ↔ pCoreJoinAction 2 hn g = 1
  rw [← coreMap_spec]
  exact (map_eq_one_iff (MulAut.conj : (L ⧸ pCore 2 L) →* MulAut (L ⧸ pCore 2 L))
    (Theory.GroupTheory.conj_injective_of_center_eq_bot hc)).symm

/-- Simplicity of the concrete PSL₄(2) quotient and perfectness kill its center. -/
theorem core_center_eq_bot {I : Subgroup G} (c : ComponentWitness d I)
    (model : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) :
    center (c.L ⧸ pCore 2 c.L) = ⊥ := by
  let _ : IsSimpleGroup (Projective 4) := Atlas.psl_simple_high_rank 4 (by decide)
  let _ : IsSimpleGroup (c.L ⧸ pCore 2 c.L) := model.isSimpleGroup
  let _ := c.core_quotient_quasisimple
  exact (inferInstance : (center (c.L ⧸ pCore 2 c.L)).Normal).eq_bot_or_eq_top.resolve_right
    (fun h => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h))


/-- The source elementary span lies in R, as required by B.2.4. -/
theorem span_le_R (hW : d.componentSpan L ≤ L ⊔ d.R)
    (hred : IsR2Within (d.componentSpan L) (L ⊔ d.R))
    (hcore : (L ⊔ d.R).pCoreIn 2 ≤ d.R) : d.componentSpan L ≤ d.R := by
  let _ := hred.normal
  let _ := hred.elementary
  have hw : (d.componentSpan L).subgroupOf (L ⊔ d.R) ≤ pCore 2 (L ⊔ d.R : Subgroup G) :=
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 _⟩
  have hm := map_mono (f := (L ⊔ d.R).subtype) hw
  rw [map_subgroupOf_eq_of_le hW] at hm
  exact hm.trans hcore

/-- Two-reducedness kills the two-core action on the original span. -/
theorem core_centralizes_internal_span
    (hred : IsR2Within (d.componentSpan L) (L ⊔ d.R)) :
    pCore 2 (L ⊔ d.R : Subgroup G) ≤
      centralizer ((d.componentSpan L).subgroupOf (L ⊔ d.R) : Set (L ⊔ d.R : Subgroup G)) := by
  let _ := hred.normal
  let q := QuotientGroup.mk' (centralizer
    ((d.componentSpan L).subgroupOf (L ⊔ d.R) : Set (L ⊔ d.R : Subgroup G)))
  have hn : ((pCore 2 (L ⊔ d.R : Subgroup G)).map q).Normal :=
    Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hp : (pCore 2 (L ⊔ d.R : Subgroup G)).map q ≤ pCore 2 _ :=
    le_sSup ⟨hn, pCore_isPGroup.map q⟩
  rw [hred.reduced] at hp
  simpa only [q, QuotientGroup.ker_mk'] using
    (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hp)

include hn in
/-- Both defining factors of U_L are LR-invariant, so U_L is too. -/
theorem commutator_normalizes (hW : d.componentSpan L ≤ L ⊔ d.R)
    (hred : IsR2Within (d.componentSpan L) (L ⊔ d.R)) :
    L ⊔ d.R ≤ normalizer (spanCommutator d L : Set G) := by
  have hw := (normal_subgroupOf_iff_le_normalizer hW).mp hred.normal
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    (mem_normalizer_iff_map_conj_eq.mp (hw hg)),
    (mem_normalizer_iff_map_conj_eq.mp ((sup_le L.le_normalizer hn) hg))]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Offenders

end
