module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.NormalForms.Products2

/-!
# Packed transition certificates for the 27 local J4 normal forms

Each equality checks the right action of one of the two proposed generators
on the packed rows, using kernel reduction and the proved packed multiplication
algorithm. The row witnesses and ATLAS source attribution are in `Matrices.Rows`.
Transport to the actual group words additionally requires their matrix evaluations.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

theorem normalRows_mul_u (t : Fin 3 × Fin 3 × Fin 3) :
    packedMul (normalRows t) uRows = normalRows (t.1 + 1, t.2.1, t.2.2 - t.2.1) := by
  rcases t with ⟨i, j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact normal000_mul_u
  · exact normal001_mul_u
  · exact normal002_mul_u
  · exact normal010_mul_u
  · exact normal011_mul_u
  · exact normal012_mul_u
  · exact normal020_mul_u
  · exact normal021_mul_u
  · exact normal022_mul_u
  · exact normal100_mul_u
  · exact normal101_mul_u
  · exact normal102_mul_u
  · exact normal110_mul_u
  · exact normal111_mul_u
  · exact normal112_mul_u
  · exact normal120_mul_u
  · exact normal121_mul_u
  · exact normal122_mul_u
  · exact normal200_mul_u
  · exact normal201_mul_u
  · exact normal202_mul_u
  · exact normal210_mul_u
  · exact normal211_mul_u
  · exact normal212_mul_u
  · exact normal220_mul_u
  · exact normal221_mul_u
  · exact normal222_mul_u

theorem normalRows_mul_v (t : Fin 3 × Fin 3 × Fin 3) :
    packedMul (normalRows t) vRows = normalRows (t.1, t.2.1 + 1, t.2.2) := by
  rcases t with ⟨i, j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact normal000_mul_v
  · exact normal001_mul_v
  · exact normal002_mul_v
  · exact normal010_mul_v
  · exact normal011_mul_v
  · exact normal012_mul_v
  · exact normal020_mul_v
  · exact normal021_mul_v
  · exact normal022_mul_v
  · exact normal100_mul_v
  · exact normal101_mul_v
  · exact normal102_mul_v
  · exact normal110_mul_v
  · exact normal111_mul_v
  · exact normal112_mul_v
  · exact normal120_mul_v
  · exact normal121_mul_v
  · exact normal122_mul_v
  · exact normal200_mul_v
  · exact normal201_mul_v
  · exact normal202_mul_v
  · exact normal210_mul_v
  · exact normal211_mul_v
  · exact normal212_mul_v
  · exact normal220_mul_v
  · exact normal221_mul_v
  · exact normal222_mul_v

end Janko4.Simplicity.ThreeLocalCertificates
