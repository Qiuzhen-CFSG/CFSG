module

public import Theory.Representation.BinaryPermutation.EightOrthogonalActors
public import Theory.Representation.BinaryPermutation.EightGeometry
public import Theory.Representation.BinaryOffender.Basic

/-!
# Fixed codimension of a four-group on the deleted eight-point module

The polar perpendicular of the common fixed space contains every
displacement. If the fixed codimension is at most two, a nonidentity even
involution makes that perpendicular a plane. The orthogonal plane-movement
theorem then bounds the elementary actor by two elements, excluding order
four. No conjugacy type of the four-group is assumed.
Source application: Aschbacher--Smith 12.9.4, printed p.860.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open BinaryPermutation

/-- An elementary four-group in A₈ has fixed codimension at least three on
the actual six-dimensional deleted permutation module. -/
theorem deleted_eight_four_fixedCodim_gt_two
    (A : Subgroup (Equiv.Perm (Fin 8))) (hA : A ≤ alternatingGroup (Fin 8))
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hcard : Nat.card A = 4) :
    2 < fixedCodim (naturalRepresentation (Fin 8)) A := by
  by_contra! hsmall
  let ρ := naturalRepresentation (Fin 8)
  let B := TerminalOrthogonal.Eight.form.polarBilin
  let P := LinearMap.BilinForm.orthogonal B (fixedSpace ρ A)
  have hmove : ∀ a ∈ A, (ρ a - LinearMap.id).range ≤ P := by
    intro a ha z hz
    obtain ⟨v, rfl⟩ := hz
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro y hy
    have hf : B (ρ a y) (ρ a v) = B y v := by
      simp only [B, ρ, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        ← map_add, TerminalOrthogonal.Eight.form_invariant]
    have hy' : ρ a y = y := hy ⟨a, ha⟩
    rw [hy'] at hf
    change B y (ρ a v - v) = 0
    rw [map_sub, hf, sub_self]
  have hdim : finrank (ZMod 2) P = fixedCodim ρ A := by
    change finrank (ZMod 2) (LinearMap.BilinForm.orthogonal B (fixedSpace ρ A)) = _
    rw [LinearMap.BilinForm.finrank_orthogonal EightGeometry.polar_nondegenerate]
    have he := fixedCodim_add_finrank ρ A
    omega
  have hneA : A ≠ ⊥ := by
    intro he
    rw [he, Nat.card_unique] at hcard
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneA
  have hlo := EightOrthogonalActors.two_le_displacement a (hA a.property)
    (fun he => ha (Subtype.ext he)) (hsq a a.property)
  change 2 ≤ finrank (ZMod 2) (ρ a - LinearMap.id).range at hlo
  have hle := Submodule.finrank_mono (hmove a a.property)
  have hP : finrank (ZMod 2) P = 2 := by
    change fixedCodim ρ A ≤ 2 at hsmall
    omega
  have hbound := EightOrthogonalActors.card_le_two_of_plane_displacement
    A hA hsq P hP hmove
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
