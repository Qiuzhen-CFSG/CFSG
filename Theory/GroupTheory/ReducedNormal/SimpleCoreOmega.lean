module
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleKernel
public import Theory.GroupTheory.ReducedNormal.Basic
public import Stellmacher.OmegaOneCenterMap

/-!
# Omega-centers in extensions of simple two-core quotients

A perfect two-core extension of a simple group has no ordinary component
unless it is itself quasisimple. Its radical is its two-core, so in the
other case its generalized Fitting subgroup equals that core.

For a normal C-component with centerless quasisimple two-core quotient
and a two-group supplement, nontrivial action on the ambient omega-center
forces its full centralizer to be the two-core. The normal-kernel bound
also makes the omega-center reduced; every reduced subgroup lies inside
it. These are the group-theoretic steps used with the literal K_vS action
in Aschbacher--Smith, Lemma 12.6.13(1), printed p.826.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {C : Type*} [Group C] [Finite C] [Group.IsPerfect C]
  [IsSimpleGroup (C ⧸ pCore 2 C)] [IsQuasisimple (C ⧸ pCore 2 C)]
/-- A perfect two-core extension of a simple group has characteristic two unless it is quasisimple. -/
theorem constrained_of_simple_core_not_quasisimple
    (hp : IsPPerfect 2 C) (hn : ¬ IsQuasisimple C) :
    generalizedFitting C = pCore 2 C := by
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 C) pCore_isPGroup hp
  have he : componentLayer C = ⊥ := by
    apply sSup_eq_bot.mpr
    intro J hJ
    have hJtop : J = ⊤ := hJ.isCComponent.eq_of_le ht le_top
    let : IsQuasisimple (⊤ : Subgroup C) := hJtop ▸ hJ.2
    exact (hn (IsQuasisimple.of_mulEquiv topEquiv)).elim
  rw [generalizedFitting,he,sup_bot_eq]
  apply le_antisymm _ (pCore_le_fitting C 2)
  rw [←PerfectCoreTwoExtension.radical_eq_core (G := C)]
  exact le_solvableRadical _ inferInstance inferInstance
end Theory.GroupTheory
namespace Theory.GroupTheory
variable {B : Type*} [Group B] [Finite B]
/-- A moved omega-center detects the full simple component quotient and is the maximal reduced subgroup. -/
theorem omegaCenter_reduced_of_simple_component
    (C S : Subgroup B) [C.Normal] (hC : C.IsCComponent)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hz : center (C ⧸ pCore 2 C) = ⊥)
    (hS : IsPGroup 2 S) (hgen : C ⊔ S = ⊤)
    (hm : ⁅omegaOneCenterAmbient (pCore 2 B), C⁆ ≠ ⊥) :
    centralizer (omegaOneCenterAmbient (pCore 2 B) : Set B) = pCore 2 B ∧
      omegaOneCenterAmbient (pCore 2 B) = reducedTwoSubgroup B := by
  let W := omegaOneCenterAmbient (pCore 2 B)
  let : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian _
  let : W.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro b _
    rw [mem_normalizer_iff_map_conj_eq]
    change (omegaOneCenterAmbient (pCore 2 B)).map (MulAut.conj b).toMonoidHom = _
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj b).injective]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp
      ((le_normalizer_of_normal : (⊤ : Subgroup B) ≤ normalizer (pCore 2 B : Set B)) (mem_top b))
  have hQN : pCore 2 B ≤ centralizer (W : Set B) := by
    intro b hb w hw
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 b hb |>.symm
  have hCN : ¬ C ≤ centralizer (W : Set B) := by
    intro hc
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hk := QuasisimpleKernel.normal_kernel_structure C S (centralizer (W : Set B))
    hC hS hgen hQN hCN
  have he : centralizer (W : Set B) = pCore 2 B := by
    apply le_antisymm _ hQN
    have hbound := hk.1
    rw [hz, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hbound
    exact hbound.trans (sup_le le_rfl (pCoreIn_le_of_subnormal 2 hC.subnormal))
  have hr : IsPReduced 2 W := ⟨inferInstance, inferInstance, hk.2⟩
  refine ⟨he,le_antisymm hr.le_reducedPSubgroup ?_⟩
  let : IsElementaryAbelian 2 (reducedTwoSubgroup B) := isPReduced_reducedPSubgroup.elementary
  intro r hr
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨reducedPSubgroup_le_pCore 2 B hr,
      elemPow_eq_one_of_isElementaryAbelian r hr,
      reducedPSubgroup_le_centralizer_pCore 2 B hr⟩
end Theory.GroupTheory
