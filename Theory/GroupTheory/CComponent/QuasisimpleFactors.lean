module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Quasisimple residual factors and conjugacy bounds

Ordinary components are C-components. When each factor's solvable residual
is trivial or quasisimple, the C-components of their direct product are
precisely among the two embedded residuals: perfectness places a component
in their join, and the component dichotomy forces containment in one factor.
A normal overgroup can therefore only permute these two subgroups.

The intrinsic generalized Fitting subgroup is characteristic. Thus when it
is quasisimple, it is a C-component whose image in every normal overgroup
has exactly one conjugate. This does not require the whole subgroup to be
perfect or quasisimple.

Source: the component calculus of GLS, volume 2, Chapter 1, as used in
Aschbacher–Smith B.5.6 and 15.3.49(i), printed pp.105 and 1143–1144.
The generalized-Fitting transport proof is adapted from this repository's
`Theory.Mathieu.M22.ValueBoundParabolics.Transport`.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem IsComponent.isCComponent {L : Subgroup G} (hL : IsComponent G L) :
    L.IsCComponent := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  refine ⟨(nontrivial_iff_ne_bot L).mp inferInstance, inferInstance, hL.1, ?_⟩
  intro K hKL hK hp hsub
  rcases IsQuasisimple.subnormal_le_center_or_eq_top
      (K.subgroupOf L) hsub.subgroupOf with hc | ht
  · let := hp
    let : Group.IsPerfect (K.subgroupOf L) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKL).symm.toMonoidHom)
        (subgroupOfEquivOfLe hKL).symm.surjective
    have hb : K.subgroupOf L = ⊥ := by
      rw [← commutator_eq_self (H := K.subgroupOf L)]
      exact le_bot_iff.mp ((commutator_mono hc le_top).trans
        (commutator_center_left (⊤ : Subgroup L)).le)
    have he := congrArg (map L.subtype) hb
    exact (hK (by simpa only [map_subgroupOf_eq_of_le hKL, Subgroup.map_bot] using he)).elim
  · exact subgroupOf_eq_top.mp ht

private theorem map_generalizedFitting_le_equiv (e : G ≃* H) :
    (generalizedFitting G).map e.toMonoidHom ≤ generalizedFitting H := by
  rw [generalizedFitting, Subgroup.map_sup]
  apply sup_le
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply sSup_le
    rintro N ⟨hn, hnil⟩
    apply (Subgroup.map_le_iff_le_comap).mp
    apply le_trans _ (fitting_le_generalizedFitting H)
    let := hnil
    exact le_sSup ⟨hn.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
  · apply (Subgroup.map_le_iff_le_comap).mpr
    apply sSup_le
    intro N hn
    exact (Subgroup.map_le_iff_le_comap).mp
      (component_le_generalizedFitting H _ (hn.map_equiv e))

theorem map_generalizedFitting_equiv (e : G ≃* H) :
    (generalizedFitting G).map e.toMonoidHom = generalizedFitting H := by
  apply le_antisymm (map_generalizedFitting_le_equiv e)
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_generalizedFitting_le_equiv e.symm)
  have hi : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  simpa only [Subgroup.map_map, hi, Subgroup.map_id] using h

instance generalizedFitting_characteristic : (generalizedFitting G).Characteristic :=
  characteristic_iff_map_eq.mpr map_generalizedFitting_equiv

theorem cComponent_eq_of_pair_cover (B C : Subgroup G)
    (hB : B = ⊥ ∨ IsComponent G B) (hC : C = ⊥ ∨ IsComponent G C)
    {K : Subgroup G} (hK : K.IsCComponent) (hle : K ≤ B ⊔ C) :
    K = B ∨ K = C := by
  have step (D : Subgroup G) (hD : D = ⊥ ∨ IsComponent G D) :
      K = D ∨ ⁅D, K⁆ = ⊥ := by
    rcases hD with rfl | hD
    · exact Or.inr (commutator_bot_left K)
    rcases hD.subnormal_dichotomy K hK.subnormal with h | h
    · exact Or.inl (hD.isCComponent.eq_of_le hK h).symm
    · exact Or.inr h
  rcases step B hB with h | hb
  · exact Or.inl h
  rcases step C hC with h | hc
  · exact Or.inr h
  have hcomm : ⁅B ⊔ C, K⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer] at hb hc ⊢
    exact sup_le hb hc
  let := hK.perfect
  exact (hK.ne_bot (le_bot_iff.mp (by
    calc K = ⁅K, K⁆ := (commutator_eq_self (H := K)).symm
         _ ≤ ⁅B ⊔ C, K⁆ := commutator_mono hle le_rfl
         _ = ⊥ := hcomm))).elim

variable (N : Subgroup G) [N.Normal]

theorem normal_cComponent_conjugates_pair (B C : Subgroup N)
    (hclass : ∀ K : Subgroup N, K.IsCComponent → K = B ∨ K = C)
    {K : Subgroup N} (hK : K.IsCComponent) (g : G) :
    (K.map N.subtype).map (MulAut.conj g).toMonoidHom = B.map N.subtype ∨
    (K.map N.subtype).map (MulAut.conj g).toMonoidHom = C.map N.subtype := by
  let L := (K.map N.subtype).map (MulAut.conj g).toMonoidHom
  have hL : L.IsCComponent :=
    (hK.map_subtype (inferInstance : N.Normal).isSubnormal).map_equiv (MulAut.conj g)
  have hLN : L ≤ N := by
    rintro _ ⟨k, ⟨a, ha, rfl⟩, rfl⟩
    exact (inferInstance : N.Normal).conj_mem a a.property g
  rcases hclass (L.subgroupOf N) (hL.subgroupOf hLN) with hb | hc
  · exact Or.inl (by rw [← hb, map_subgroupOf_eq_of_le hLN])
  · exact Or.inr (by rw [← hc, map_subgroupOf_eq_of_le hLN])

theorem normal_cComponent_orbit_le_two [Finite G] (B C : Subgroup N)
    (hclass : ∀ K : Subgroup N, K.IsCComponent → K = B ∨ K = C)
    {K : Subgroup N} (hK : K.IsCComponent) :
    (Set.range fun g : G => (K.map N.subtype).map (MulAut.conj g).toMonoidHom).ncard ≤ 2 := by
  have hs : (Set.range fun g : G =>
      (K.map N.subtype).map (MulAut.conj g).toMonoidHom) ⊆
      {B.map N.subtype, C.map N.subtype} := by
    rintro _ ⟨g, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      normal_cComponent_conjugates_pair N B C hclass hK g
  apply (Set.ncard_le_ncard hs).trans
  by_cases he : B.map N.subtype = C.map N.subtype
  · simp only [he, Set.pair_eq_singleton, Set.ncard_singleton]; decide
  · rw [Set.ncard_pair he]

omit [N.Normal] in
theorem generalizedFitting_isCComponent [IsQuasisimple (generalizedFitting N)] :
    (generalizedFitting N).IsCComponent :=
  (show IsComponent N (generalizedFitting N) from
    ⟨(inferInstance : (generalizedFitting N).Normal).isSubnormal, inferInstance⟩).isCComponent

theorem generalizedFitting_normal_conjugate (g : G) :
    ((generalizedFitting N).map N.subtype).map (MulAut.conj g).toMonoidHom =
      (generalizedFitting N).map N.subtype :=
  normal_iff_map_conj_eq.mp inferInstance g

theorem generalizedFitting_normal_orbit :
    (Set.range fun g : G =>
      ((generalizedFitting N).map N.subtype).map (MulAut.conj g).toMonoidHom).ncard = 1 := by
  simp only [generalizedFitting_normal_conjugate, Set.range_const, Set.ncard_singleton]

end Theory.GroupTheory

namespace Subgroup
open Theory.GroupTheory
variable {D E : Type*} [Group D] [Group E]

noncomputable def residualLeftEquiv :
    (solvableResidual D).prod (⊥ : Subgroup E) ≃* solvableResidual D :=
  (prodEquiv _ _).trans .prodUnique

noncomputable def residualRightEquiv :
    (⊥ : Subgroup D).prod (solvableResidual E) ≃* solvableResidual E :=
  (prodEquiv _ _).trans .uniqueProd

theorem residualLeft_component (hq : IsQuasisimple (solvableResidual D)) :
    IsComponent (D × E) ((solvableResidual D).prod (⊥ : Subgroup E)) := by
  let := hq
  exact ⟨(inferInstance : ((solvableResidual D).prod (⊥ : Subgroup E)).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv residualLeftEquiv.symm⟩

theorem residualRight_component (hq : IsQuasisimple (solvableResidual E)) :
    IsComponent (D × E) ((⊥ : Subgroup D).prod (solvableResidual E)) := by
  let := hq
  exact ⟨(inferInstance : ((⊥ : Subgroup D).prod (solvableResidual E)).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv residualRightEquiv.symm⟩

theorem isPerfect_le_residual_pair (K : Subgroup (D × E)) [Group.IsPerfect K] :
    K ≤ (solvableResidual D).prod (⊥ : Subgroup E) ⊔
      (⊥ : Subgroup D).prod (solvableResidual E) := by
  let : Group.IsPerfect (K.map (MonoidHom.fst D E)) := Group.IsPerfect.map _
  let : Group.IsPerfect (K.map (MonoidHom.snd D E)) := Group.IsPerfect.map _
  rintro ⟨d, e⟩ hk
  have hd := le_solvableResidual_of_isPerfect (K.map (MonoidHom.fst D E))
    (mem_map_of_mem _ hk)
  have he := le_solvableResidual_of_isPerfect (K.map (MonoidHom.snd D E))
    (mem_map_of_mem _ hk)
  have h1 : (d, (1 : E)) ∈ (solvableResidual D).prod (⊥ : Subgroup E) := ⟨hd, rfl⟩
  have h2 : ((1 : D), e) ∈ (⊥ : Subgroup D).prod (solvableResidual E) := ⟨rfl, he⟩
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
    ((solvableResidual D).prod (⊥ : Subgroup E) ⊔
      (⊥ : Subgroup D).prod (solvableResidual E)).mul_mem
      (mem_sup_left h1) (mem_sup_right h2)

theorem cComponent_eq_residual_factor
    (hD : solvableResidual D = ⊥ ∨ IsQuasisimple (solvableResidual D))
    (hE : solvableResidual E = ⊥ ∨ IsQuasisimple (solvableResidual E))
    {K : Subgroup (D × E)} (hK : K.IsCComponent) :
    K = (solvableResidual D).prod (⊥ : Subgroup E) ∨
      K = (⊥ : Subgroup D).prod (solvableResidual E) := by
  let := hK.perfect
  apply cComponent_eq_of_pair_cover _ _ _ _ hK (isPerfect_le_residual_pair K)
  · rcases hD with h | h
    · exact Or.inl (by rw [h, bot_prod_bot])
    · exact Or.inr (residualLeft_component h)
  · rcases hE with h | h
    · exact Or.inl (by rw [h, bot_prod_bot])
    · exact Or.inr (residualRight_component h)
end Subgroup
