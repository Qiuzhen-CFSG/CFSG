module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.Model
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.FiniteStructure.Generated

/-!
# Finite structure of the literal Held 2A derived subgroup

The checked perfect index-two subgroup equals the actual derived subgroup
of the literal fixed subgroup. The 21 projective labels are precisely its
orbit of letter 26. Transporting the constructed matrix projection identifies
its kernel with the unchanged orbit kernel, proving order four and centrality.
The literal centralizer has order 161280 by its independent exhaustion
certificate. Together these give all four finite-structure obligations in
`full_certificate`. The exported generator lifts also discharge the
projective-comparison theorem.

All numerical inputs are kernel-checked word certificates or previously
proved group orders. Source: GLS3 Table 5.3p, printed p.277, with the
perfect-cover convention on pp.260–261; see `FiniteStructure/Source/README.md`.
-/

@[expose] public section
open Subgroup
namespace Held.InvolutionFixedData.TwoA.FiniteStructure
open CentralizerCertificate ProjectiveComparison

/-- The order of the literal fixed subgroup, proved by finite exhaustion. -/
theorem centralizer_card : Nat.card centralizer = 161280 :=
  CentralizerCertificate.centralizer_card

noncomputable def candidateEquiv : candidate ≃* derived :=
  MulEquiv.subgroupCongr candidate_eq_derived

instance derived_perfect : Group.IsPerfect derived :=
  Group.IsPerfect.ofSurjective (f := candidateEquiv.toMonoidHom) candidateEquiv.surjective

theorem derived_card : Nat.card derived = 80640 :=
  (Nat.card_congr candidateEquiv.symm.toEquiv).trans candidate_card

theorem derived_index : derived.index = 2 := by
  rw [← candidate_eq_derived]
  exact candidate_index

theorem generator_lifts : GeneratorLifts :=
  ⟨candidateEquiv xK, candidateEquiv yK, x_labels, y_labels⟩

theorem label_mem_orbit (p : PG) : label p ∈ MulAction.orbit derived (25 : Fin 2058) := by
  have h := labels_mem_orbit label _ projective_pair_generates
    (label_generator_lifts generator_lifts) (pointEquiv 0) p
  simpa only [label_pointEquiv, pointLabel_zero] using h

theorem orbit_in_labels (v : PointOrbit) : ∃ p : PG, label p = v.val := by
  obtain ⟨d, hd⟩ := v.property
  refine ⟨candidateProjection (candidateEquiv.symm d) • pointEquiv 0, ?_⟩
  have h := candidateProjection_agrees (candidateEquiv.symm d) (pointEquiv 0)
  rw [label_pointEquiv, pointLabel_zero] at h
  exact h.symm.trans hd

noncomputable def labelOrbitEquiv : PG ≃ PointOrbit :=
  Equiv.ofBijective (fun p => ⟨label p, label_mem_orbit p⟩)
    ⟨fun _ _ h => label_injective (congrArg Subtype.val h),
      fun v => by obtain ⟨p, hp⟩ := orbit_in_labels v; exact ⟨p, Subtype.ext hp⟩⟩

theorem pointOrbit_card : Nat.card PointOrbit = 21 :=
  (Nat.card_congr labelOrbitEquiv.symm).trans card_PG

theorem orbitKernel_iff (d : derived) :
    d ∈ orbitKernel ↔ candidateEquiv.symm d ∈ candidateProjection.ker := by
  rw [mem_orbitKernel, mem_candidateProjection_ker]
  constructor
  · intro h p
    exact h ⟨label p, label_mem_orbit p⟩
  · intro h v
    obtain ⟨p, hp⟩ := orbit_in_labels v
    have hh := h p
    change representation d.val.val (label p) = label p at hh
    rwa [hp] at hh

noncomputable def kernelEquiv : orbitKernel ≃* candidateProjection.ker where
  toFun g := ⟨candidateEquiv.symm g.val, (orbitKernel_iff g.val).mp g.property⟩
  invFun g := ⟨candidateEquiv g.val, (orbitKernel_iff _).mpr (by
    simpa only [MulEquiv.symm_apply_apply] using g.property)⟩
  left_inv g := Subtype.ext (candidateEquiv.apply_symm_apply g.val)
  right_inv g := Subtype.ext (candidateEquiv.symm_apply_apply g.val)
  map_mul' g h := Subtype.ext (candidateEquiv.symm.map_mul g.val h.val)

theorem orbitKernel_card : Nat.card orbitKernel = 4 :=
  (Nat.card_congr kernelEquiv.toEquiv).trans kernel_card

theorem orbitKernel_central : orbitKernel ≤ Subgroup.center derived := by
  intro g hg
  have hz := kernel_central ((orbitKernel_iff g).mp hg)
  rw [Subgroup.mem_center_iff]
  intro d
  apply candidateEquiv.symm.injective
  simpa only [map_mul] using Subgroup.mem_center_iff.mp hz (candidateEquiv.symm d)

/-- The checked finite inputs discharge the existing projective comparison. -/
theorem orbitImage_equiv : Nonempty (orbitImage ≃* Matrix.PSL3Four.PSL) :=
  nonempty_equiv_of_generator_lifts centralizer_card orbitKernel_card generator_lifts

/-- The three finite obligations for the literal Held 2A cover. -/
theorem certificate : Group.IsPerfect derived ∧ Nat.card orbitKernel = 4 ∧
    orbitKernel ≤ Subgroup.center derived :=
  ⟨derived_perfect, orbitKernel_card, orbitKernel_central⟩

/-- All four concrete finite-structure facts for the canonical Held 2A model. -/
theorem full_certificate : Group.IsPerfect derived ∧ Nat.card centralizer = 161280 ∧
    Nat.card orbitKernel = 4 ∧ orbitKernel ≤ Subgroup.center derived :=
  ⟨derived_perfect, centralizer_card, orbitKernel_card, orbitKernel_central⟩

end Held.InvolutionFixedData.TwoA.FiniteStructure
