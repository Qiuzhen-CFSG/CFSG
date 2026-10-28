module

public import Theory.SpecificGroups.OrthogonalFourBinary.IndexTwoNormalizer.Geometry
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The six nonsingular vectors of the split binary four-space

Independent rotations of the two anisotropic planes and their interchange
act transitively on the six nonsingular vectors. Every vector is a sum of
at most two such vectors. The order of the full isometry group follows
from its nine-point singular orbit and the previously computed stabilizer
of order eight.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
O₄⁺(2) action used in Lemma 16.5.12, printed pp.1200–1201.
-/

@[expose] public section

set_option synthInstance.maxSize 10000

namespace OrthogonalFourBinary

open MulAction Theory.AlgebraicGroup

private abbrev O := IndexTwoNormalizer.IsometryGroup

/-- The actual full quadratic isometry group has order 72. -/
theorem isometryGroup_card : Nat.card IndexTwoNormalizer.IsometryGroup = 72 := by
  let v : Space := ((1, 0), (1, 0))
  have hv : v ≠ 0 := by decide +kernel
  have hqv : form v = 0 := by decide +kernel
  have he : orbit O v = {w : Space | w ≠ 0 ∧ form w = 0} := by
    ext w
    constructor
    · rintro ⟨e, rfl⟩
      refine ⟨?_, ?_⟩
      · exact fun hz => hv (e.val.injective (hz.trans (map_zero e.val).symm))
      · exact ((mem_quadraticIsometrySubgroup form _).mp e.property v).trans hqv
    · rintro ⟨hw, hqw⟩
      obtain ⟨e, he⟩ := exists_isometry_of_singular v w hv hw hqv hqw
      exact ⟨⟨e.toLinearEquiv,
        (mem_quadraticIsometrySubgroup form _).mpr e.map_app'⟩, he⟩
  have hc : Nat.card (orbit O v) = 9 := by
    rw [he, Nat.card_eq_fintype_card]
    decide +kernel
  have hs := IndexTwoNormalizer.singular_stabilizer_card v hv hqv
  have hh := Nat.card_congr (orbitProdStabilizerEquivGroup O v)
  rw [Nat.card_prod, hc, hs] at hh
  exact hh.symm

private def rotation : Plane ≃ₗ[F] Plane where
  toFun x := (x.2, x.1 + x.2)
  invFun x := (x.1 + x.2, x.1)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

private abbrev Code := Fin 3 × Fin 3 × Bool

private def candidate (i : Code) : Space ≃ₗ[F] Space :=
  ((rotation ^ (i.1 : ℕ)).prodCongr (rotation ^ (i.2.1 : ℕ))) *
    (if i.2.2 then LinearEquiv.prodComm F Plane Plane else 1)

private theorem candidate_form : ∀ i : Code, ∀ v : Space,
    form (candidate i v) = form v := by decide +kernel

private theorem candidate_transitive : ∀ v w : Space,
    form v = 1 → form w = 1 → ∃ i : Code, candidate i v = w := by decide +kernel

/-- Actual quadratic isometries are transitive on nonsingular vectors. -/
theorem exists_isometry_of_nonsingular (v w : Space)
    (hv : form v = 1) (hw : form w = 1) :
    ∃ e : IndexTwoNormalizer.IsometryGroup, e.val v = w := by
  obtain ⟨i, hi⟩ := candidate_transitive v w hv hw
  exact ⟨⟨candidate i, (mem_quadraticIsometrySubgroup form _).mpr
    (candidate_form i)⟩, hi⟩

/-- Exactly six vectors are nonsingular. -/
theorem nonsingular_card : Nat.card {v : Space // form v = 1} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Each vector is a sum of two nonsingular vectors, allowing equal summands. -/
theorem sum_two_nonsingular (v : Space) :
    ∃ a b : Space, form a = 1 ∧ form b = 1 ∧ v = a + b := by
  have h : ∀ v : Space, ∃ a b : Space, form a = 1 ∧
      form b = 1 ∧ v = a + b := by decide +kernel
  exact h v

end OrthogonalFourBinary
