module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Certificates
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Descent
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Coverage
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Characteristic
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Obstructions
public import Theory.GroupTheory.IntrinsicRadicalTransport

/-!
# Intrinsic-radical kernel intersections in the second Held model

Subgroups inside the transfer kernel have characteristic intersection trivially.
For the others, complete conjugacy coverage and the representative automorphism
calculation imply the assertion. Normality of the kernel and exceptional
subgroup makes the conclusions invariant under conjugation in the Sylow group.
The canonical subgroup equivalence then transports back to actual subgroups
of `NonsplitModels.Second`, including the precise relative normalizer action.

The checked coverage theorem, 25 intrinsic characteristicity proofs and 19
outside normalizer two-core witnesses discharge every certificate input to
`ForceNormalizer.candidateProperty`. The remaining representative is the named
exceptional subgroup. This proves the concrete intermediate assertion for the
transfer argument toward Huppert--Blackburn III, XII.1.18(b), printed p.314.
The ambient transport and recognition theorem are separate from this assertion.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer
open Subgroup

private theorem characteristic_of_equiv
    {A B : Type*} [Group A] [Group B] (M : Subgroup A) (N : Subgroup B)
    (e : A ≃* B) (hmem : ∀ x, e x ∈ N ↔ x ∈ M) (hN : N.Characteristic) :
    M.Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  have h := characteristic_iff_le_comap.mp hN (MulAut.congr e a) ((hmem x).mpr hx)
  change e (a (e.symm (e x))) ∈ N at h
  rw [e.symm_apply_apply] at h
  exact (hmem (a x)).mp h

private theorem centric_map
    {A B : Type*} [Group A] [Group B] (U : Subgroup A) (e : A ≃* B)
    (hc : centralizer (U : Set A) ≤ U) :
    centralizer (U.map e.toMonoidHom : Set B) ≤ U.map e.toMonoidHom := by
  intro x hx
  refine ⟨e.symm x, hc ?_, e.apply_symm_apply x⟩
  rw [mem_centralizer_iff]
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    mem_centralizer_iff.mp hx (e y) (mem_map_of_mem e.toMonoidHom hy)

namespace Candidates

/-- Conjugation preserves the restricted transfer kernel, so characteristicity
of its intersection can be checked on a conjugacy representative. -/
public theorem characteristic_of_conjugate (U : Subgroup Model.sylowSubgroup)
    (g : Model.sylowSubgroup)
    (hc : (kernel.subgroupOf (U.map (MulAut.conj g).toMonoidHom)).Characteristic) :
    (kernel.subgroupOf U).Characteristic := by
  apply characteristic_of_equiv _ _ ((MulAut.conj g).subgroupMap U) _ hc
  intro x
  have h := mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective (K := kernel) (x := (x : Model.sylowSubgroup))
  have hm : kernel.map (MulAut.conj g).toMonoidHom = kernel :=
    normal_iff_map_conj_eq.mp kernel_normal g
  rw [hm] at h
  exact h

/-- Since the exceptional subgroup is normal in the Sylow group, its conjugacy
class contains only itself. -/
public theorem eq_exceptional_of_conjugate (U : Subgroup Model.sylowSubgroup)
    (g : Model.sylowSubgroup) (hU : U.map (MulAut.conj g).toMonoidHom = exceptional) :
    U = exceptional := by
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have hm : exceptional.map (MulAut.conj g).toMonoidHom = exceptional :=
    normal_iff_map_conj_eq.mp exceptional_normal g
  rw [hU, hm]

/-- The two finite certificate obligations imply the assertion on actual
subgroups of the Sylow carrier. Both obligations remain explicit here. -/
public theorem property_of_coverage (hcover : Coverage) (hrep : RepresentativeProperty)
    (U : Subgroup Model.sylowSubgroup)
    (hc : centralizer (U : Set Model.sylowSubgroup) ≤ U)
    (hr : IntrinsicRadical U) :
    (kernel.subgroupOf U).Characteristic ∨ U = exceptional := by
  classical
  by_cases hUK : U ≤ kernel
  · left
    rw [subgroupOf_eq_top.mpr hUK]
    infer_instance
  · obtain ⟨i, g, hg⟩ := hcover U hc hUK
    have hc' := centric_map U (MulAut.conj g) hc
    have hr' := (intrinsic_radical_map_equiv_iff (MulAut.conj g) U 2).mpr hr
    rw [hg] at hc' hr'
    rcases hrep i hc' hr' with hk | he
    · left
      apply characteristic_of_conjugate U g
      rwa [hg]
    · exact Or.inr (eq_exceptional_of_conjugate U g (hg.trans he))

end Candidates

/-- Certified coverage and representative automorphism checks give exactly
`CandidateProperty` for subgroups of `Second`, with the displayed relative
centralizer and intrinsic normalizer-action hypotheses. -/
public theorem candidateProperty_of_coverage
    (hcover : Candidates.Coverage) (hrep : Candidates.RepresentativeProperty) :
    CandidateProperty := by
  intro U hUS hc hr
  let V := U.subgroupOf Model.sylowSubgroup
  have hcV : centralizer (V : Set Model.sylowSubgroup) ≤ V := by
    intro x hx
    apply hc
    refine ⟨x.property, ?_⟩
    change (x : NonsplitModels.Second) ∈ centralizer (U : Set NonsplitModels.Second)
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (mem_centralizer_iff.mp hx (⟨y, hUS hy⟩ : Model.sylowSubgroup) hy)
  have hrV : Candidates.IntrinsicRadical V :=
    (intrinsic_radical_subgroupOf_iff U Model.sylowSubgroup hUS 2).mpr hr
  rcases Candidates.property_of_coverage hcover hrep V hcV hrV with hk | he
  · left
    apply characteristic_of_equiv _ _ (subgroupOfEquivOfLe hUS).symm _ hk
    intro x
    rfl
  · right
    have hm := congrArg (fun W : Subgroup Model.sylowSubgroup => W.map Model.sylowSubgroup.subtype) he
    exact (map_subgroupOf_eq_of_le hUS).symm.trans
      (hm.trans (map_subgroupOf_eq_of_le Model.exceptionalSubgroup_le_sylow))

/-- Reduction to the three independent finite certificates. -/
public theorem candidateProperty_of_certificates
    (hcover : Candidates.Coverage) (hchar : Candidates.CharacteristicChecks)
    (hobs : Candidates.ObstructionChecks) : CandidateProperty :=
  candidateProperty_of_coverage hcover
    (Candidates.representativeProperty_of_certificates hchar hobs)

/-- Every centric intrinsic-radical subgroup of the fixed Sylow subgroup has
characteristic intersection with the transfer kernel, unless it is the named
exceptional subgroup. All coverage and automorphism certificates are discharged. -/
public theorem candidateProperty : CandidateProperty :=
  candidateProperty_of_certificates Candidates.coverage
    Candidates.characteristicChecks Candidates.obstructionChecks

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer
