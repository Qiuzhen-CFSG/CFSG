module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree44.Orbits

/-!
# Degree-44 simplicity for the M₁₁ coset factor

The packed columns use exactly `Data.modelMatrix`, acting on column vectors.
All finite identities are checked by the Lean kernel. The low-rank operator
and the orbit bases are reproduced by `source/discover.py` and `export.py`.
Source context: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree44
open Matrix

theorem simple (U : Submodule (ZMod 2) (Fin 44 → ZMod 2))
    (h : ∀ s v, v ∈ U → (Data.modelMatrix 3 s).mulVec v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hA : ∀ s, Preserves U (matrix (generators s)) := by
    intro s
    rw [generators_eq]
    exact h s
  apply simple_of_detects U hA
  intro x hx hn
  apply top_of_peak U peak (peak_preserves U hA) (vector 10780052908951) (vector 0)
    (vector 10589135643391) (vector 0) peak_eq (columns_top U hA) ?_ x hx hn
  simpa only [vector_zero, add_zero] using columns_top U hA

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.FactorSimplicity.Degree44
