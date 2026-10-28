module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Marks
import all Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Marks

/-!
# Orders of the literal canonical shared pair

The actual two canonical point generators have orders three and four;
their product has order five. These are equations in the original PSL3(4)
quotient, with scalar ambiguity checked on the same native matrices.
-/

public noncomputable section
namespace Matrix.PSL3Four.MathieuAmalgamMarking

/-- The same canonical pair has the literal orders needed to mark its
alternating-five quotient as a (3,2,5) pair. -/
theorem canonical_pair_orders :
    orderOf (pair 0)=3 ∧ orderOf (pair 1)=4 ∧ orderOf (pair 0*pair 1)=5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h0 : nativePair 0^3=1 := by decide +kernel
  have h1 : nativePair 1^4=1 := by decide +kernel
  have h01 : (nativePair 0*nativePair 1)^5=1 := by decide +kernel
  have hn0 : pair 0≠1 := by
    rw [ne_eq,pair,project_eq_one_iff]
    decide +kernel
  have hn1 : (pair 1)^2≠1 := by
    change (project (nativePair 1))^2≠1
    rw [←map_pow,ne_eq,project_eq_one_iff]
    decide +kernel
  have hn01 : pair 0*pair 1≠1 := by
    change project (nativePair 0)*project (nativePair 1)≠1
    rw [←map_mul,ne_eq,project_eq_one_iff]
    decide +kernel
  refine ⟨orderOf_eq_prime ?_ hn0,orderOf_eq_prime_pow (p:=2) (n:=1) (by simpa using hn1) ?_,
    orderOf_eq_prime ?_ hn01⟩
  · exact (map_pow project (nativePair 0) 3).symm.trans ((congrArg project h0).trans project.map_one)
  · exact (map_pow project (nativePair 1) 4).symm.trans ((congrArg project h1).trans project.map_one)
  · change (project (nativePair 0)*project (nativePair 1))^5=1
    rw [←map_mul,←map_pow,h01,map_one]

end Matrix.PSL3Four.MathieuAmalgamMarking
