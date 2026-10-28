module
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.CoreActors
public import Theory.GroupTheory.Recognition.QuasithinM23.CoreRestriction
public import Theory.GroupTheory.Recognition.QuasithinM23.CoreDetermination
public import Theory.Mathieu.M23.QuasithinGeometry.StandardSystem
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
/-!
# Aligning the full heptad core without losing the edge

The action image of the pair/heptad intersection is self-normalizing, so every
core-preserving automorphism restricts to conjugation by that intersection.
If it also preserves the edge intersection, self-centralization of the core
forces the conjugator to normalize this intersection. A double transposition
recovers its fixed triple and shows that the whole native edge fixer is
normalized as well.

All maps use the literal native subgroups. Source: Aschbacher--Smith 5.2.20(5),
printed pp.656--657, the alignment preceding full-Ix correction.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M23Geometry
private abbrev H := pairStabilizer.subgroupOf heptadStabilizer
private theorem core_le_H : heptadKernel ≤ H := by
  intro u hu
  exact (heptadKernelAmbient_le_twoPair ⟨u,hu,rfl⟩).1.2

/-- Every automorphism of the pair/heptad intersection preserving its full
core restricts to conjugation by an element of that same intersection. -/
theorem heptad_pair_core_automorphism_realized
    (α : MulAut (pairStabilizer.subgroupOf heptadStabilizer))
    (hα : (heptadKernel.subgroupOf (pairStabilizer.subgroupOf heptadStabilizer)).map
      α.toMonoidHom = heptadKernel.subgroupOf (pairStabilizer.subgroupOf heptadStabilizer)) :
    ∃ g : pairStabilizer.subgroupOf heptadStabilizer, ∀ u : heptadKernel,
      (α ⟨u,(heptadKernelAmbient_le_twoPair ⟨u,u.property,rfl⟩).1.2⟩ : heptadStabilizer) =
        g.val * u.val * g.val⁻¹ := by
  let i : heptadKernel →* H := inclusion core_le_H
  let a : H →* MulAut heptadKernel :=
    (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel).comp H.subtype
  have ha (g : H) (u : heptadKernel) : i (a g u) = g * i u * g⁻¹ := by
    apply Subtype.ext
    exact MulAut.conjNormal_apply g.val u
  let N := heptadKernel.subgroupOf H
  let e : N ≃* heptadKernel := subgroupOfEquivOfLe core_le_H
  let c : MulAut heptadKernel := e.symm.trans
    ((α.subgroupMap N).trans ((MulEquiv.subgroupCongr hα).trans e))
  have hc (u : heptadKernel) : α (i u) = i (c u) := rfl
  have hr : a.range = H.map (MulAut.conjNormal : heptadStabilizer →* MulAut heptadKernel) := by
    rw [MonoidHom.range_comp,range_subtype]
  have hn : normalizer (a.range : Set _) = a.range := by
    rw [hr]
    exact heptad_pair_core_action_self_normalizing
  obtain ⟨g,hg⟩ := Theory.GroupTheory.QuasithinM23.core_automorphism_realized
    i (inclusion_injective core_le_H) a ha hn α c hc
  exact ⟨g,fun u => congrArg Subtype.val (hg u)⟩

open scoped Pointwise
private theorem edge_fixes (g : M23) : g ∈ standardSystem.edgeGroup ↔
    g • label 4 = label 4 ∧ g • label 5 = label 5 ∧ g • label 6 = label 6 := by
  rw [standardSystem_edgeGroup]
  constructor
  · rintro ⟨hp,hy⟩
    obtain ⟨h56,h4⟩ := (mem_adjacent_stabilizer_iff ⟨g,hp⟩).mp hy
    exact ⟨congrArg Subtype.val h4,(mem_pointwisePairStabilizer ⟨g,hp⟩).mp h56⟩
  · rintro ⟨h4,h5,h6⟩
    have hp : g ∈ pairStabilizer := by
      change g • x.val = x.val
      change g • ({label 5,label 6} : Finset (Fin 23)) = _
      simp only [Finset.smul_finset_insert,Finset.smul_finset_singleton,h5,h6]
      rfl
    refine ⟨hp,(mem_adjacent_stabilizer_iff ⟨g,hp⟩).mpr ?_⟩
    exact ⟨(mem_pointwisePairStabilizer ⟨g,hp⟩).mpr ⟨h5,h6⟩,Subtype.ext h4⟩

private theorem edge_heptad_fixes (g : heptadStabilizer) :
    (g : M23) ∈ standardSystem.edgeGroup ↔
      ∀ k ∈ ({4,5,6} : Set (Fin 7)), heptadAction g k = k := by
  rw [edge_fixes]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,forall_eq_or_imp,forall_eq,
    ←heptadAction_apply,label.injective.eq_iff]

/-- Normalizing the edge intersection inside the heptad local normalizes the
whole native edge fixer. The double transposition recovers its fixed triple. -/
theorem heptad_edge_intersection_normalizer (g : heptadStabilizer)
    (hg : g ∈ normalizer (standardSystem.edgeGroup.subgroupOf heptadStabilizer :
      Set heptadStabilizer)) :
    (g : M23) ∈ normalizer (standardSystem.edgeGroup : Set M23) := by
  let b : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3,by change Equiv.Perm.sign _ = 1; decide⟩
  let s := AlternatingSection.s b
  have hb : s ∈ standardSystem.edgeGroup.subgroupOf heptadStabilizer := by
    apply (edge_heptad_fixes s).mpr
    rw [AlternatingSection.heptadAction_s]
    decide +kernel
  have hc := (mem_normalizer_iff''.mp hg s).mp hb
  have ht : heptadAction g • ({4,5,6} : Set (Fin 7)) = {4,5,6} := by
    apply (MulAction.mem_stabilizer_set' (Set.toFinite _)).mpr
    intro k hk
    have hh := (edge_heptad_fixes (g⁻¹*s*g)).mp hc k hk
    have hh' := congrArg (heptadAction g) hh
    have hfix : b.val (heptadAction g k) = heptadAction g k := by
      simpa only [map_mul,map_inv,Equiv.Perm.coe_mul,Function.comp_apply,
        Equiv.Perm.inv_def,Equiv.apply_symm_apply,s,AlternatingSection.heptadAction_s] using hh'
    have hbfix : ∀ k : Fin 7, b.val k = k → k ∈ ({4,5,6} : Set (Fin 7)) := by
      decide +kernel
    exact hbfix _ hfix
  have edge_eq : standardSystem.edgeGroup =
      fixingSubgroup M23 ({label 4,label 5,label 6} : Set (Fin 23)) := by
    ext a
    rw [edge_fixes]
    change _ ↔ ∀ i : ({label 4,label 5,label 6} : Set (Fin 23)), a • i.val = i.val
    simp only [Subtype.forall,Set.mem_insert_iff,Set.mem_singleton_iff,
      forall_eq_or_imp,forall_eq]
  have ht' : (g : M23) • ({label 4,label 5,label 6} : Set (Fin 23)) =
      {label 4,label 5,label 6} := by
    have hf : heptadAction g • ({4,5,6} : Finset (Fin 7)) = {4,5,6} := by
      apply Finset.coe_injective
      simpa only [Finset.coe_smul_finset,Finset.coe_insert,Finset.coe_singleton] using ht
    have hh := (heptadAction_stabilizes_labels g ({4,5,6} : Finset (Fin 7))).mp hf
    have hh' := congrArg (fun S : Finset (Fin 23) => (S : Set (Fin 23))) hh
    simpa only [Finset.image_insert,Finset.image_singleton,Finset.coe_smul_finset,
      Finset.coe_insert,Finset.coe_singleton] using hh'
  rw [edge_eq]
  exact mem_normalizer_iff_map_conj_eq.mpr (SubMulAction.fixingSubgroup_map_conj_eq ht')

/-- A core-preserving automorphism of the pair/heptad intersection that preserves
the edge intersection has its core restriction realized by an edge normalizer. -/
theorem heptad_pair_core_automorphism_realized_preserving_edge
    (α : MulAut (pairStabilizer.subgroupOf heptadStabilizer))
    (hα : (heptadKernel.subgroupOf (pairStabilizer.subgroupOf heptadStabilizer)).map
      α.toMonoidHom = heptadKernel.subgroupOf (pairStabilizer.subgroupOf heptadStabilizer))
    (hαE : ((standardSystem.edgeGroup.subgroupOf heptadStabilizer).subgroupOf
      (pairStabilizer.subgroupOf heptadStabilizer)).map α.toMonoidHom =
      (standardSystem.edgeGroup.subgroupOf heptadStabilizer).subgroupOf
        (pairStabilizer.subgroupOf heptadStabilizer)) :
    ∃ g : pairStabilizer.subgroupOf heptadStabilizer,
      (g.val : M23) ∈ normalizer (standardSystem.edgeGroup : Set M23) ∧
      ∀ u : heptadKernel,
      (α ⟨u,(heptadKernelAmbient_le_twoPair ⟨u,u.property,rfl⟩).1.2⟩ : heptadStabilizer) =
        g.val * u.val * g.val⁻¹ := by
  obtain ⟨g,hg⟩ := heptad_pair_core_automorphism_realized α hα
  let N := heptadKernel.subgroupOf H
  let E := standardSystem.edgeGroup.subgroupOf heptadStabilizer
  have hEH : E ≤ H := by
    intro a ha
    change (a : M23) ∈ standardSystem.edgeGroup at ha
    exact (standardSystem_edgeGroup ▸ ha).1
  have hNE : N ≤ E.subgroupOf H := by
    intro a ha
    change (a.val : M23) ∈ standardSystem.edgeGroup
    rw [standardSystem_edgeGroup]
    exact ⟨(heptadKernelAmbient_le_twoPair ⟨a.val,ha,rfl⟩).1.2,
      (heptadKernelAmbient_le_twoPair ⟨a.val,ha,rfl⟩).2⟩
  let f : H →* heptadStabilizer := H.subtype.comp α.toMonoidHom
  let c : H →* heptadStabilizer := (MulAut.conj g.val).toMonoidHom.comp H.subtype
  have hfN : N.map f = heptadKernel := by
    rw [show f = H.subtype.comp α.toMonoidHom from rfl,←map_map,hα,
      map_subgroupOf_eq_of_le core_le_H]
  have hNnormal : N.Normal := inferInstance
  have hm := Theory.GroupTheory.QuasithinM23.map_eq_of_agree_on_selfCentralizing_normal
    N (E.subgroupOf H) hNE f c (fun u => hg ⟨u.val.val,u.property⟩)
    (by rw [hfN]; exact heptadKernel_selfCentralizing)
  have hfE : (E.subgroupOf H).map f = E := by
    change (E.subgroupOf H).map (H.subtype.comp α.toMonoidHom) = _
    rw [←map_map,hαE,map_subgroupOf_eq_of_le hEH]
  have hcE : (E.subgroupOf H).map c = E.map (MulAut.conj g.val).toMonoidHom := by
    change (E.subgroupOf H).map ((MulAut.conj g.val).toMonoidHom.comp H.subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le hEH]
  have hgn : g.val ∈ normalizer (E : Set heptadStabilizer) :=
    mem_normalizer_iff_map_conj_eq.mpr (hcE.symm.trans (hm.symm.trans hfE))
  exact ⟨g,heptad_edge_intersection_normalizer g.val hgn,hg⟩
end Sporadic.Mathieu.M23Geometry
