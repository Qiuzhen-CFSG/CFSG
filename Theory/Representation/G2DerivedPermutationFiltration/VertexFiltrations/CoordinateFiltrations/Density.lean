module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Data
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Density.Transports

/-!
# Full matrix algebras on the binary vertex-coordinate factors

The literal diagonal blocks of both published flags generate all matrices.
Two explicit word-span certificates handle dimensions 14 and 6; checked
invertible intertwiners transfer those results to every other nontrivial block.
The degree-one blocks are scalar algebras. This is the density input to the
coordinate-filtration assembly for Aschbacher–Smith G.7.2(3), printed p.348.
It does not assert the separate identification with the actual quotients.
-/

@[expose] public section
namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

private theorem one_algebra_eq_top
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1) (Fin 1) (ZMod 2))) : Q = ⊤ := by
  apply top_unique
  intro M _
  have hm : M = M 0 0 • (1 : Matrix (Fin 1) (Fin 1) (ZMod 2)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hm]
  exact Q.smul_mem Q.one_mem _

/-- Every published diagonal factor has full generated binary matrix algebra. -/
theorem factorMatrix_algebra_eq_top (i : Fin 2) (t : Factor i)
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree i t)) (Fin (degree i t)) (ZMod 2)))
    (h : ∀ j, factorMatrix i t j ∈ Q) : Q = ⊤ := by
  fin_cases i
  · fin_cases t
    · exact Density.Fourteen.algebra_eq_top Q h
    · exact Density.Six.algebra_eq_top Q h
    · exact one_algebra_eq_top Q
    · exact Density.factor_0_3_algebra_eq_top Q h
    · exact Density.factor_0_4_algebra_eq_top Q h
    · exact one_algebra_eq_top Q
    · exact Density.factor_0_6_algebra_eq_top Q h
    · exact Density.factor_0_7_algebra_eq_top Q h
    · exact one_algebra_eq_top Q
  · fin_cases t
    · exact Density.factor_1_0_algebra_eq_top Q h
    · exact Density.factor_1_1_algebra_eq_top Q h
    · exact one_algebra_eq_top Q
    · exact Density.factor_1_3_algebra_eq_top Q h
    · exact one_algebra_eq_top Q
    · exact Density.factor_1_5_algebra_eq_top Q h
    · exact Density.factor_1_6_algebra_eq_top Q h
    · exact one_algebra_eq_top Q
    · exact Density.factor_1_8_algebra_eq_top Q h
    · exact one_algebra_eq_top Q
    · exact Density.factor_1_10_algebra_eq_top Q h
    · exact one_algebra_eq_top Q

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
