module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme

/-!
# The literal action of the syntheme quotient on the natural plane

The quotient maps of the full and even syntheme stabilizers are trivial
exactly when the corresponding permutation fixes the canonical binary
plane pointwise. It suffices to test the two generating duads; the checked
48-element affine block model identifies that predicate with trivial
block permutation. This connects the existing abstract S₃ quotient to
the original plane action, without replacing its representation.

Source: Aschbacher--Smith, B.3 and13.5.4, pp.84–85,916.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PlaneAction
open NaturalGeometry SynthemeCalculation

private theorem model_fixed_pairs : ∀g:Model,
    (pair (modelHom g 0) (modelHom g 1)=pair 0 1 ∧
      pair (modelHom g 2) (modelHom g 3)=pair 2 3) ↔ g.right=1 := by
  decide +kernel

private theorem fixes_plane_iff (g:Equiv.Perm (Fin 6)) :
    (∀v∈canonicalPlane,naturalRepresentation (Fin 6) g v=v) ↔
      pair (g 0) (g 1)=pair 0 1 ∧ pair (g 2) (g 3)=pair 2 3 := by
  constructor
  · intro h
    constructor
    · have hh:=h (pairVector 0 1) (Submodule.subset_span (by simp))
      rw [pairVector_map] at hh
      exact (pairVector_eq_iff (g.injective.ne (by decide)) (by decide)).mp hh
    · have hh:=h (pairVector 2 3) (Submodule.subset_span (by simp))
      rw [pairVector_map] at hh
      exact (pairVector_eq_iff (g.injective.ne (by decide)) (by decide)).mp hh
  · intro h v hv
    have h0:naturalRepresentation (Fin 6) g (pairVector 0 1)=pairVector 0 1:=by
      rw [pairVector_map]
      exact (pairVector_eq_iff (g.injective.ne (by decide)) (by decide)).mpr h.1
    have h2:naturalRepresentation (Fin 6) g (pairVector 2 3)=pairVector 2 3:=by
      rw [pairVector_map]
      exact (pairVector_eq_iff (g.injective.ne (by decide)) (by decide)).mpr h.2
    obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hv
    simp only [map_add,map_smul,h0,h2]

theorem syntheme_quotient_eq_one_iff (g:synthemeStabilizer) :
    synthemeQuotientHom g=1 ↔ ∀v∈canonicalPlane,naturalRepresentation (Fin 6) g.val v=v := by
  rw [fixes_plane_iff]
  obtain ⟨x,rfl⟩:=modelEquiv.surjective g
  rw [←MonoidHom.mem_ker,synthemeQuotientHom_ker,mem_synthemeCore_iff]
  rw [modelEquiv.symm_apply_apply]
  exact (model_fixed_pairs x).symm

theorem even_syntheme_quotient_eq_one_iff (g:a6SynthemeStabilizer) :
    a6SynthemeQuotientHom g=1 ↔ ∀v∈canonicalPlane,naturalRepresentation (Fin 6) g.val.val v=v := by
  rw [fixes_plane_iff]
  obtain ⟨x,rfl⟩:=evenModelEquiv.surjective g
  rw [←MonoidHom.mem_ker,a6SynthemeQuotientHom_ker,mem_a6SynthemeCore_iff]
  rw [evenModelEquiv.symm_apply_apply]
  exact (model_fixed_pairs x.val).symm

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PlaneAction
