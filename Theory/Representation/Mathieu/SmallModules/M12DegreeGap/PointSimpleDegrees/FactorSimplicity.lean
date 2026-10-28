module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree10
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree32
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree44
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Interface

/-!
# Simplicity of the four concrete M₁₁ eleven-coset factors

The degree-one case is elementary. For degrees 10 and 44, kernel-checked
words and sums in the two given matrices produce a rank-one operator.
For degree 32 the sum of the eleven powers of AB has rank two. Cyclic dual
bases detect nonzero invariant subspaces, and cyclic column bases show that
the detected images generate the whole space. This proves binary simplicity
without asserting absolute irreducibility in degree 32.

`simpleMatrices` discharges precisely the finite-algebra input to
`filtration_of_certificates`. The actual coset flag remains its independent
geometric input, supplied by `FlagCoordinates`; no flag is assumed in the
simplicity proof. The shared data and public interfaces are unchanged.
Source context: James, J. Algebra 27 (1973), 57–111. Reproduction and measured
kernel-check costs are in `FactorSimplicity/source/README.md`.
-/

public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity

private theorem degree_one (U : Submodule (ZMod 2) (Fin 1 → ZMod 2)) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hu : U = ⊥
  · exact Or.inl hu
  right
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
  have h0 : v 0 ≠ 0 := by
    intro h
    apply hn
    funext i
    fin_cases i
    exact h
  have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have h1 : v 0 = 1 := (binary _).resolve_left h0
  apply top_unique
  intro w _
  have he : w = w 0 • v := by
    funext i
    fin_cases i
    change w 0 = w 0 * v 0
    rw [h1, mul_one]
  rw [he]
  exact U.smul_mem _ hv

/-- All four published pairs have only zero and full common invariant
binary subspaces, with no character-table or certificate hypothesis. -/
theorem simpleMatrices : Data.SimpleMatrices := by
  intro i U h
  fin_cases i
  · exact degree_one U
  · exact Degree10.simple U h
  · exact Degree32.simple U h
  · exact Degree44.simple U h

/-- Application to the literal M₁₁ coset representation: the matrix-simplicity
premise is discharged, leaving only the independent actual-flag construction. -/
theorem factorDegreeFiltration (C : FlagCoordinates) :
    FactorDegreeFiltration ({1, 10, 32, 44} : Set ℕ) cosetRepresentation :=
  filtration_of_certificates C simpleMatrices

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity
