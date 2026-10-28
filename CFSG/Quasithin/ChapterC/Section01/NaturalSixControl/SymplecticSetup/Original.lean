module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Source
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Movement

/-!
# The original natural S6 pair realizes the symplectic source

The natural module is moved by the component, hence lies in it. Restricting
the original marked action to J = L B therefore retains the entire natural
module and fixed vector. The intrinsic MS pair supplies the edge two-group,
two-core containment and characteristic condition. The projection is exactly
the restriction of the original map into S6; the component still maps to A6.

Source: Aschbacher--Smith C.1.37 and MS93 Section 3.0. No whole-core
reconstruction or weak-BN classification is a premise of this realization.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}

namespace SourceData
variable (d : NaturalSixControl.SourceData L V T)
include d

theorem module_le_component : V ≤ L := by
  have hm := d.module_le_residual_commutator
  rw [d.component_eq_residual] at hm
  exact hm.trans (commutator_le_right V L)

/-- The original component--Baumann pair retains the marked natural action. -/
noncomputable def originalSource (h : IntrinsicMSPair d) :
    Source (L.subgroupOf (L ⊔ d.B)) (d.B.subgroupOf (L ⊔ d.B))
      (V.subgroupOf (L ⊔ d.B)) := by
  let J := L ⊔ d.B
  have hLJ : L ≤ J := le_sup_left
  have hBJ : d.B ≤ J := le_sup_right
  have hVJ : V ≤ J := (module_le_component d).trans hLJ
  have hVQ : V ≤ pCore 2 K := by
    let := d.elementary
    exact le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩
  have hp : IsPPerfect 2 L := by
    rw [← d.component_eq_residual]
    exact isPPerfect_pResidual 2
  have hp' : IsPPerfect 2 (L.subgroupOf J) := hp.of_surjective
    (subgroupOfEquivOfLe hLJ).symm.toMonoidHom (subgroupOfEquivOfLe hLJ).symm.surjective
  exact {
    two_group := h.radical.isPGroup
    core_le := h.radical.twoCore_le
    characteristic := h.characteristic
    product := by
      intro m
      obtain ⟨l,hl,r,hr,he⟩ := mem_sup_of_normal_left.mp m.property
      exact ⟨⟨l,hLJ hl⟩,hl,⟨r,hBJ hr⟩,hr,Subtype.ext he⟩
    residual := pResidual_eq_of_isPPerfect_sup _ _ hp' h.radical.isPGroup
      (codisjoint_subgroupOf_sup L d.B).eq_top
    projection := d.q.comp J.subtype
    projection_kernel := by
      change d.q.ker.comap J.subtype = pCore 2 J
      rw [d.ker_eq,d.core_product]
    component_image := by
      rw [← map_map,map_subgroupOf_eq_of_le hLJ,d.image_component]
    module_le_core := by
      intro v hv
      rw [d.core_product]
      exact hVQ hv
    module_le_component := fun _ hv => module_le_component d hv
    coordinates := (subgroupOfEquivOfLe hVJ).trans d.eV
    action := fun g w => d.action (g : K) ((subgroupOfEquivOfLe hVJ) w)
    w := ⟨⟨d.v,hVJ d.v.property⟩,d.v.property⟩
    w_ne := by
      intro he
      apply d.v_ne
      apply Subtype.ext
      exact congrArg (fun a : V.subgroupOf J => ((a : J) : K)) he
    radical_fixes := by
      intro r hr
      apply Subtype.ext
      exact d.sylow_fixes (r : K)
        (d.radical_le_sylow ((show d.B ≤ d.R from inf_le_left) hr)) }

/-- The source realization uses precisely the restriction of the original map. -/
theorem originalSource_projection (h : IntrinsicMSPair d) :
    (originalSource d h).projection = d.q.comp (L ⊔ d.B : Subgroup K).subtype := rfl

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
