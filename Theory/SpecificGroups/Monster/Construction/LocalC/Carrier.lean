module
public import Theory.SpecificGroups.Monster.Construction.LocalC.OrthogonalSpace
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.Isometry

/-!
# The fixed real Griess carrier

Instantiate the signed short-lift summand with the proved source map
`(v,J+Golay) ↦ f_v+f(J)+2Λ`. Together with the actual Parker spin tensor
summand and symmetric matrices this gives the fixed 196,884-dimensional
positive definite real space. No comparison or representation is an input.
The action of the local group is constructed separately on this carrier.

Source: Aschbacher, *Sporadic Groups*, Section 27, printed pp. 147–150.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.LocalC

/-- The source signed short-extraspecial summand. -/
abbrev BShort := ShortSpace sourceLatticeComparison

/-- The fixed carrier `B₋ ⊥ Bᵣ ⊥ Bₛ`. -/
abbrev B := OrthogonalSpace sourceLatticeComparison

/-- The explicit orthogonal sum form on the fixed carrier. -/
abbrev fixedGamma : LinearMap.BilinForm ℝ B := gamma sourceLatticeComparison

theorem bShort_finrank : Module.finrank ℝ BShort = 98280 :=
  shortSpace_finrank sourceLatticeComparison

theorem b_finrank : Module.finrank ℝ B = 196884 :=
  orthogonalSpace_finrank sourceLatticeComparison

theorem fixedGamma_apply (v w : B) : fixedGamma v w =
    minusForm v.1 w.1 + shortForm sourceLatticeComparison v.2.1 w.2.1 +
      symmetricGamma v.2.2 w.2.2 := rfl

theorem fixedGamma_symmetric (v w : B) : fixedGamma v w = fixedGamma w v :=
  gamma_symmetric sourceLatticeComparison v w

theorem fixedGamma_pos (v : B) (hv : v ≠ 0) : 0 < fixedGamma v v :=
  gamma_pos sourceLatticeComparison v hv

theorem fixedGamma_eq_zero_iff (v : B) : fixedGamma v v = 0 ↔ v = 0 :=
  gamma_eq_zero_iff sourceLatticeComparison v

end Sporadic.Monster.Construction.LocalC
