module

public import Theory.GroupTheory.InvertedOddLift

/-!
# The faithful inverted three-lift in Lemma 14.1.18

In the star quotient, the reflection centralizes the kernel of the map to S₃.
Use the odd lift obtained from a product of conjugate involutions. Its cube
lies in that kernel, so the reflection both fixes and inverts the cube.
The cube has odd order and square one, and consequently is trivial. The
lift therefore has order exactly three and retains its order-three image.

No two-group hypothesis on the action kernel is imposed. This supplies the
lifting calculation in Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), printed p.981, Lemma 14.1.18.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries

/-- A reflection centralizing the action kernel has a faithful inverted three-lift. -/
public theorem inverted_three_lift_of_centralizing_kernel
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (w : H) (hw : w ^ 2 = 1) (hfw : f w ≠ 1)
    (hcentral : ∀ k ∈ f.ker, w * k = k * w) :
    ∃ y : H, orderOf y = 3 ∧ orderOf (f y) = 3 ∧ w * y * w⁻¹ = y⁻¹ := by
  obtain ⟨y, hodd, himage, hinv⟩ :=
    exists_inverted_odd_of_surjective_perm_three f hf w hw hfw
  have hyker : y ^ 3 ∈ f.ker := by
    change f (y ^ 3) = 1
    rw [map_pow]
    simpa only [himage] using pow_orderOf_eq_one (f y)
  have hfix : w * y ^ 3 * w⁻¹ = y ^ 3 := by
    rw [hcentral _ hyker, mul_inv_cancel_right]
  have hinv3 : w * y ^ 3 * w⁻¹ = (y ^ 3)⁻¹ := by
    change MulAut.conj w (y ^ 3) = (y ^ 3)⁻¹
    rw [map_pow]
    change (w * y * w⁻¹) ^ 3 = (y ^ 3)⁻¹
    rw [hinv, inv_pow]
  have hy6 : y ^ (3 * 2) = 1 := by
    rw [pow_mul, pow_two]
    calc
      y ^ 3 * y ^ 3 = (y ^ 3)⁻¹ * y ^ 3 :=
        congrArg (fun a => a * y ^ 3) (hfix.symm.trans hinv3)
      _ = 1 := inv_mul_cancel _
  have hd : orderOf y ∣ 3 :=
    hodd.coprime_two_right.dvd_mul_right.mp (orderOf_dvd_of_pow_eq_one hy6)
  have heq : orderOf y = 3 := Nat.dvd_antisymm hd (himage ▸ orderOf_map_dvd f y)
  exact ⟨y, heq, himage, hinv⟩
end CFSG.Quasithin.Chapter14.SourcePreliminaries
