module
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Symplectic

/-!
# The actual symplectic form and the invariant hyperplane

The coordinate dot product on the six-letter augmentation quotient is
alternating and nondegenerate and is preserved by every coordinate permutation.
The orthogonal of a Borel-invariant hyperplane is an invariant line. The proved
uniqueness of that line identifies the hyperplane with its perpendicular.

This establishes the marking used in Aschbacher–Smith 13.8.7, printed p.949,
from the natural action and invariant flag of Notation 13.2.1 and Remark 13.5.3.
Neither the perpendicular marking nor form preservation is an assumption.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
open BinaryPermutation
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

private theorem orthogonal_invariant (D : Submodule (ZMod 2) (natural (Fin 6)))
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

/-- The orthogonal of every Borel-invariant hyperplane is its unique fixed line.
Thus the source's invariant flag determines the orthogonal marking. -/
theorem invariant_hyperplane_eq_orthogonal
    (Z D : Submodule (ZMod 2) (natural (Fin 6)))
    (hZ : Module.finrank (ZMod 2) Z = 1)
    (hD : Module.finrank (ZMod 2) D = 3)
    (hZi : ∀ g ∈ T0, Submodule.map (naturalRepresentation (Fin 6) g) Z = Z)
    (hDi : ∀ g ∈ T0, Submodule.map (naturalRepresentation (Fin 6) g) D = D) :
    D = form.orthogonal Z := by
  have hd : Module.finrank (ZMod 2) (form.orthogonal D) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide), hD]
    rfl
  have hline : form.orthogonal D = Z :=
    (canonicalLine_unique _ hd (fun g hg => orthogonal_invariant D g (hDi g hg))).trans
      (canonicalLine_unique Z hZ hZi).symm
  rw [← hline, LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl]

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair.CoverGeometry
end
