module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.NativeSuzukiChart
public import Theory.Representation.Suzuki.NaturalMatrix

/-!
# The corrected Suzuki root matrix on the natural module

The matrix chart and the Ree presentation chart differ by the triangular
change (a,b) ↦ (a,b+a·θ(a)). Expanding that correction and using θ²(a)=a²
gives the complete four-coordinate action in the source convention θ=titsEnd.
The proof is symbolic and includes the field of order two. PinnedNatural
applies it to both literal Section 10 source quotient actions.

Source: Fong--Seitz II (1974), (10.7) and (10.11), pp.223--224;
the Suzuki chart convention is recorded before (10.32), p.230.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

private theorem natural_raw_root (m : ℕ) (a b : CoefficientField m)
    (v : Representation.SuzukiNatural.W m) :
    Representation.SuzukiNatural.natural m (matrixRootPoint m a b : SuzukiMatrixGroup m) v =
      ![v 0+a*v 1+b*v 2+(a^(2+2^(m+1))+a*b+b^(2^(m+1)))*v 3,
        v 1+a^(2^(m+1))*v 2+(a^(1+2^(m+1))+b)*v 3,v 2+a*v 3,v 3] := by
  ext i
  fin_cases i <;> simp [Representation.SuzukiNatural.natural_apply,matrixRootPoint,
    SuzukiRootGL,SuzukiRootMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_four,add_assoc]

/-- The corrected whole Suzuki chart acts by this matrix, in the source
θ = titsEnd convention, including the field of order two. -/
theorem natural_corrected_root (m : ℕ) (a b : CoefficientField m)
    (v : Representation.SuzukiNatural.W m) :
    Representation.SuzukiNatural.natural m
      (matrixRootPoint m a (b+a*titsEnd m a) : SuzukiMatrixGroup m) v =
      ![v 0 + a*v 1 + (b+a*titsEnd m a)*v 2 +
          (a^2*titsEnd m a+a*b+titsEnd m b)*v 3,
        v 1 + titsEnd m a*v 2 + b*v 3,
        v 2 + a*v 3, v 3] := by
  rw [natural_raw_root]
  have hp (z : CoefficientField m) : z^(2^(m+1)) = titsEnd m z := rfl
  have hp1 : a^(1+2^(m+1)) = a*titsEnd m a := by rw [pow_add,pow_one,hp]
  have hp2 : a^(2+2^(m+1)) = a^2*titsEnd m a := by rw [pow_add,hp]
  simp only [hp1,hp2,hp,map_add,map_mul,titsEnd_twice]
  ext i
  fin_cases i
  · dsimp
    linear_combination (norm := ring_nf)
      (a^2*v 3) * CharTwo.add_self_eq_zero (titsEnd m a)
  · dsimp
    linear_combination (norm := ring_nf)
      (a*v 3) * CharTwo.add_self_eq_zero (titsEnd m a)
  · rfl
  · rfl

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
