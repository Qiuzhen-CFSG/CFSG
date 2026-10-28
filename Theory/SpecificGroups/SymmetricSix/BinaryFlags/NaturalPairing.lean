module

public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The pairing and hyperplanes of the binary natural six-letter module

The dot product on the augmentation core descends to an alternating,
nondegenerate form on the actual quotient. Every coordinate permutation
preserves this form, so a subspace stabilizer preserves its perpendicular.
For the canonical alternating Sylow subgroup, uniqueness of the invariant
line identifies the invariant hyperplane with that line's perpendicular.

These reusable proofs are adapted from the existing project module
`CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CoverSymplecticGeometry.Form`,
which is preserved. The original natural quotient and its permutation action
are used throughout; no abstract symplectic-model identification is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§B.3, printed pp.83–85, and Notation 13.2.1, printed p.877.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
noncomputable abbrev form : LinearMap.BilinForm (ZMod 2) (natural (Fin 6)) :=
  naturalPairing (Fin 6)

/-- The descended coordinate form is alternating because representatives have even sum. -/
theorem form_alt : form.IsAlt := by
  intro v
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  rw [naturalPairing_apply_core]
  have hs (c : ZMod 2) : c * c = c := by fin_cases c <;> rfl
  simp_rw [hs]
  exact a.property

/-- The coordinate form is preserved by the entire symmetric action. -/
theorem form_invariant (g : Equiv.Perm (Fin 6)) (v w : natural (Fin 6)) :
    form (naturalRepresentation (Fin 6) g v) (naturalRepresentation (Fin 6) g w) =
      form v w := by
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  obtain ⟨b, rfl⟩ := coreToNatural_surjective w
  rw [← coreToNatural_equivariant, ← coreToNatural_equivariant,
    naturalPairing_apply_core, naturalPairing_apply_core]
  change (∑ i, a.val (g.symm i) * b.val (g.symm i)) = ∑ i, a.val i * b.val i
  exact Equiv.sum_comp g.symm (fun i => a.val i * b.val i)

theorem form_nondegenerate : form.Nondegenerate := by
  have hn (x : natural (Fin 6)) (hx : ∀ y, form x y = 0) : x = 0 := by
    apply naturalPairing_injective (Fin 6)
    ext y
    simpa only [map_zero, LinearMap.zero_apply] using hx y
  exact ⟨hn, fun x hx => hn x (fun y => form_alt.eq_iff.mp (hx y))⟩

theorem orthogonal_invariant (D : Submodule (ZMod 2) (natural (Fin 6)))
    (g : Equiv.Perm (Fin 6))
    (hD : Submodule.map (naturalRepresentation (Fin 6) g) D = D) :
    Submodule.map (naturalRepresentation (Fin 6) g) (form.orthogonal D) =
      form.orthogonal D := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩ y hy
    obtain ⟨z, hz, rfl⟩ := (hD.symm ▸ hy : y ∈ Submodule.map (naturalRepresentation (Fin 6) g) D)
    rw [form_invariant]
    exact hx z hz
  · exact (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((naturalRepresentation (Fin 6)).asGroupHom g)).finrank_map_eq _


/-- Membership in a representation's stabilizer is equivalent to equality of images. -/
theorem mem_stabilizer_iff_map (P : Submodule (ZMod 2) V) (g : S) :
    g ∈ subspaceStabilizer (naturalRepresentation Ω) P ↔
      P.map (naturalRepresentation Ω g) = P := by
  constructor
  · intro hg
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hg v).mpr hv
    · intro v hv
      refine ⟨naturalRepresentation Ω g⁻¹ v, ?_, ?_⟩
      · exact ((subspaceStabilizer (naturalRepresentation Ω) P).inv_mem hg v).mpr hv
      · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Module.End.one_apply]
  · intro hg v
    constructor
    · intro hv
      obtain ⟨w, hw, he⟩ := hg.symm ▸ hv
      have hi := (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((naturalRepresentation Ω).asGroupHom g)).injective he
      exact hi ▸ hw
    · intro hv
      rw [← hg]
      exact Submodule.mem_map_of_mem hv

/-- Stabilizing a subspace also stabilizes its perpendicular in the actual pairing. -/
theorem stabilizer_le_orthogonal_stabilizer (P : Submodule (ZMod 2) V) :
    subspaceStabilizer (naturalRepresentation Ω) P ≤
      subspaceStabilizer (naturalRepresentation Ω) (form.orthogonal P) := by
  intro g hg
  exact (mem_stabilizer_iff_map _ _).mpr
    (orthogonal_invariant P g ((mem_stabilizer_iff_map _ _).mp hg))

/-- A canonical Sylow-invariant hyperplane is the perpendicular of its invariant line. -/
theorem invariant_hyperplane_eq_orthogonal
    (P D : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1)
    (hD : Module.finrank (ZMod 2) D = 3)
    (hPi : T0 ≤ subspaceStabilizer (naturalRepresentation Ω) P)
    (hDi : T0 ≤ subspaceStabilizer (naturalRepresentation Ω) D) :
    D = form.orthogonal P := by
  have hd : Module.finrank (ZMod 2) (form.orthogonal D) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide), hD]
    rfl
  have hline : form.orthogonal D = P :=
    (canonicalLine_unique _ hd (fun g hg => orthogonal_invariant D g
      ((mem_stabilizer_iff_map _ _).mp (hDi hg)))).trans
      (canonicalLine_unique P hP (fun g hg =>
        (mem_stabilizer_iff_map _ _).mp (hPi hg))).symm
  rw [← hline, LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl]
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
