module

public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup

/-!
# The intrinsic Sylow and parabolic reduction for G₂ automorphisms

Sylow conjugacy corrects any abstract automorphism to preserve the standard
positive-root subgroup. Its central involutions and second-central involutions
recover the highest-root subgroup and the two-long-root subgroup. Their
normalizers are the two standard parabolics, so the corrected automorphism
preserves both labels, without an automorphism classification hypothesis.

This is the initial geometric reduction toward inner-field coverage; it does
not yet make all eight individual root groups invariant.

Source: Aschbacher--Smith 2.3.9(7), printed p.526, and the automorphism input
used in F.1.12, printed pp.263--264. The intrinsic characterizations and
normalizer equalities are proved in the imported ATLAS-port extensions.
-/

@[expose] public section

open scoped Pointwise
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open Subgroup LieParabolicSetup SylowParabolicInvariance
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem parabolics_invariant_of_sylow (a : MulAut (Model F))
    (ha : unipotent.map a.toMonoidHom = unipotent) :
    parabolic₁.map a.toMonoidHom = parabolic₁ ∧
      parabolic₂.map a.toMonoidHom = parabolic₂ := by
  have hA := map_eq_of_centralInvolutions unipotent highestRoot
    highestRoot_iff_centralInvolution a ha
  have hB := map_eq_of_secondCentralInvolutions unipotent longRootLocal
    longRootLocal_iff_secondCentralInvolution a ha
  constructor
  · rw [← normalizer_highestRoot, map_equiv_normalizer_eq, hA]
  · rw [← normalizer_longRootLocal, map_equiv_normalizer_eq, hB]

theorem exists_sylow_parabolic_alignment (a : MulAut (Model F)) :
    ∃ g : Model F,
      unipotent.map (MulAut.conj g * a).toMonoidHom = unipotent ∧
      parabolic₁.map (MulAut.conj g * a).toMonoidHom = parabolic₁ ∧
      parabolic₂.map (MulAut.conj g * a).toMonoidHom = parabolic₂ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F)
    (a • sylow (F := F)) (sylow (F := F))
  have hU : unipotent.map (MulAut.conj g * a).toMonoidHom = unipotent := by
    have h := congrArg (fun S : Sylow 2 (Model F) => (S : Subgroup (Model F))) hg
    change (((sylow (F := F) : Subgroup (Model F)).map a.toMonoidHom).map
      (MulAut.conj g).toMonoidHom) = _ at h
    rw [map_map, sylow_coe] at h
    exact h
  exact ⟨g, hU, parabolics_invariant_of_sylow _ hU⟩

end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
