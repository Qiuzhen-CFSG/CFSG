module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.OrthogonalSix
import Mathlib.Tactic.FinCases

/-!
# The actual exterior action on the split orthogonal six-space

The six retained wedge coordinates have the same two-by-two minors as the
upper four-by-four block. Removing the other four, vanishing coordinates
therefore identifies the restricted exterior action with the compound action.
The Pfaffian isometry consequently intertwines this action with the established
SL₄(2) ≃ Ω⁺₆(2) comparison, for the repository's actual Omega subgroup.

Source: Aschbacher–Smith, Lemma 12.5.2(4), printed p.817/PDF p.834.
The orthogonal model and comparison are from the attributed ATLAS port imported
by `OrthogonalSix`; its license is recorded there.
-/

@[expose] public noncomputable section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional Atlas.Order20160A8.Bivectors

private theorem v6_pair (i : Fin 6) :
    pair (v6Index i) 0 = (first i).castSucc ∧
      pair (v6Index i) 1 = (second i).castSucc := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

private theorem v6_minor (g : Group) (i j : Fin 6) :
    actionMatrix g (v6Index i) (v6Index j) = compound (upperBlock g) i j := by
  simp only [actionMatrix, compound, (v6_pair i).1, (v6_pair i).2,
    (v6_pair j).1, (v6_pair j).2, upperBlock]
  rw [mul_comm (g.val (second i).castSucc (first j).castSucc)]

/-- The literal exterior action restricts to the compound matrix of the upper block. -/
theorem v6Coordinates_action (g : parabolic 4) (v : V₆) :
    v6Coordinates (v6Action g v) =
      exteriorMap (upperBlock g.val) (v6Coordinates v) := by
  have hv := (mem_coordinateSpan _ _).mp v.property
  have v3 := hv 3 (by decide)
  have v6 := hv 6 (by decide)
  have v8 := hv 8 (by decide)
  have v9 := hv 9 (by decide)
  ext i
  change coordinates (exteriorAction 2 g.val v.val) (v6Index i) = _
  rw [coordinates_action]
  change (∑ j : Fin 10, actionMatrix g.val (v6Index i) j * coordinates v.val j) =
    ∑ j : Fin 6, compound (upperBlock g.val) i j * v6Coordinates v j
  simp_rw [← v6_minor, v6Coordinates_apply]
  simp [Fin.sum_univ_succ, v6Index, v3, v6, v8, v9, -coordinates_apply]

/-- The quadratic isometry intertwines the actual parabolic action with Ω⁺₆(2). -/
theorem v6QuadraticIsometry_action (g : parabolic 4) (v : V₆) :
    v6QuadraticIsometry (v6Action g v) =
      (sl4TwoOmegaEquiv (parabolicFourBlock g)).val.val (v6QuadraticIsometry v) := by
  rw [sl4TwoOmegaEquiv_linear]
  change Atlas.Order20160A8.Exterior.coordinates (v6Coordinates (v6Action g v)) =
    Atlas.Order20160A8.Exterior.coordinates
      (exteriorMap (upperBlock g.val)
        (Atlas.Order20160A8.Exterior.coordinates.symm
          (Atlas.Order20160A8.Exterior.coordinates (v6Coordinates v))))
  rw [LinearEquiv.symm_apply_apply, v6Coordinates_action]


/-- The actual restricted exterior action preserves the Pfaffian on V₆. -/
theorem v6QuadraticForm_invariant (g : parabolic 4) (v : V₆) :
    v6QuadraticForm (v6Action g v) = v6QuadraticForm v := by
  change pfaffian (v6Coordinates (v6Action g v)) = pfaffian (v6Coordinates v)
  rw [v6Coordinates_action, pfaffian_exteriorMap, upperBlock_det g.val g.property, one_mul]

end Representation.SL5ExteriorSquare
