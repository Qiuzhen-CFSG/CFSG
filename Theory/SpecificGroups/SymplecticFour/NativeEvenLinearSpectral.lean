module
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# No characteristic-two PSL₃ in symplectic four-space

The explicit binary Singer cycle and its squaring normalizer map through
the prime field into SL₃(K). The cycle remains nonidentity projectively:
its off-diagonal entry is one, whereas every central SL₃ matrix is scalar.
The order-seven symplectic spectral obstruction excludes a faithful map
from the actual PSL₃(K) carrier, over every characteristic-two field K.

Source: the degree-four inspection in Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.NativeEvenLinearSpectral
private def a : SL(3,ZMod 2) := ⟨!![0,0,1;1,0,1;0,1,0],by decide⟩
private def b : SL(3,ZMod 2) := ⟨!![1,0,0;0,0,1;0,1,1],by decide⟩
variable {K F : Type*} [Field K] [CharP K 2] [Field F] [CharP F 2]
/-- The literal PSL₃ action cannot be a faithful symplectic four-space action. -/
theorem pslThree_not_injective (j : PSL(3,K) →* Sp F) : ¬Function.Injective j := by
  intro hj
  let r : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let p : SL(3,ZMod 2) →* PSL(3,K) :=
    (QuotientGroup.mk' (Subgroup.center SL(3,K))).comp (SpecialLinearGroup.map r)
  have hpa : p a ≠ 1 := by
    intro h
    have hc : SpecialLinearGroup.map r a ∈ Subgroup.center SL(3,K) :=
      (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨c,_,hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hc
    change (0:K)=r 1 at he
    exact zero_ne_one (he.trans r.map_one)
  let f := j.comp p
  apply SevenNormalizer.seven_not_conjugate_square (f a) (f b)
  · rw [←map_pow, show a^7=1 by decide +kernel,map_one]
  · exact fun h => hpa (hj (h.trans j.map_one.symm))
  · simpa only [map_mul,map_inv,map_pow] using
      congrArg f (by decide +kernel : b*a*b⁻¹=a^2)
end Theory.SpecificGroups.SymplecticFour.NativeEvenLinearSpectral
