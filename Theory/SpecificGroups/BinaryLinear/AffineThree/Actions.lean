module

public import Theory.SpecificGroups.BinaryLinear.AffineThree.Coordinates
public import Theory.SpecificGroups.BinaryLinear.AffineThree.QuaternionFactors

/-!
# Cubic and swapping actors in the actual affine centralizer

The block-diagonal SL₂(2) subgroup acts by the literal matrix multiplication.
Its cubic acts on the Heisenberg core as the checked fixed-center automorphism,
and its involution acts as the factor swap. Thus every quaternion subgroup
of the intrinsic two-core is nonnormal in this point centralizer.

Source: Aschbacher–Smith 12.2.27(2), using I.4.6 (pp.807,417).
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open Subgroup Matrix
namespace BinaryLinear.Affine.ThreeLocal
open ThreeCore

def liftHom : SL2 →* H where
  toFun := lift
  map_one' := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · simp [lift]
    · apply Subtype.ext
      ext i j
      change (liftMatrix (g*h)).val i j = ((liftMatrix g).val * (liftMatrix h).val) i j
      fin_cases i <;> fin_cases j <;>
        simp [liftMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ]

theorem liftHom_injective : Function.Injective liftHom := by
  intro g h he
  have hh := congrArg projection he
  simpa only [show ∀ g, liftHom g = lift g from fun _ => rfl, projection_lift] using hh

def cubicMatrix : SL2 := ⟨!![1,1;1,0], by decide +kernel⟩
def swapMatrix : SL2 := ⟨!![0,1;1,0], by decide +kernel⟩
def cubicActor : H := lift cubicMatrix
def swapActor : H := lift swapMatrix

theorem cubicMatrix_order : orderOf cubicMatrix = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

theorem cubicActor_order : orderOf cubicActor = 3 :=
  (orderOf_injective liftHom liftHom_injective cubicMatrix).trans cubicMatrix_order

theorem cubic_intertwines (q : Q) : cubicActor * embed q = embed (cubic q) * cubicActor := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (0 + (liftMatrix cubicMatrix).val.mulVec ![q.z,q.c,q.d]) =
      Multiplicative.ofAdd (![q.z,q.c+q.d,q.c] + (upper q.b (q.a+q.b)).val.mulVec 0)
    congr 1
    ext i
    fin_cases i <;> simp [liftMatrix,cubicMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · apply Subtype.ext
    ext i j
    change ((liftMatrix cubicMatrix).val * (upper q.a q.b).val) i j =
      ((upper q.b (q.a+q.b)).val * (liftMatrix cubicMatrix).val) i j
    fin_cases i <;> fin_cases j <;>
      simp [liftMatrix,cubicMatrix,upper,Matrix.mul_apply,Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals simp [show (2 : ZMod 2) = 0 from rfl]

theorem swap_intertwines (q : Q) : swapActor * embed q = embed (swap q) * swapActor := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (0 + (liftMatrix swapMatrix).val.mulVec ![q.z,q.c,q.d]) =
      Multiplicative.ofAdd (![q.z,q.d,q.c] + (upper q.b q.a).val.mulVec 0)
    congr 1
    ext i
    fin_cases i <;> simp [liftMatrix,swapMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · apply Subtype.ext
    ext i j
    change ((liftMatrix swapMatrix).val * (upper q.a q.b).val) i j =
      ((upper q.b q.a).val * (liftMatrix swapMatrix).val) i j
    fin_cases i <;> fin_cases j <;>
      simp [liftMatrix,swapMatrix,upper,Matrix.mul_apply,Fin.sum_univ_succ]

theorem swap_conjugation (q : Q) : swapActor * embed q * swapActor⁻¹ = embed (swap q) := by
  rw [swap_intertwines, mul_inv_cancel_right]

theorem quaternion_nonnormal (R : Subgroup (pCore 2 H))
    (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    ¬ (R.map (pCore 2 H).subtype).Normal := by
  let S := R.map coreEquiv.symm.toMonoidHom
  have hS : Nonempty (S ≃* QuaternionGroup 2) :=
    ⟨(coreEquiv.symm.subgroupMap R).symm.trans hR.some⟩
  have hh := quaternion_nonnormal_of_swap embed embed_injective swapActor swap_conjugation S hS
  have he : S.map embed = R.map (pCore 2 H).subtype := by
    dsimp only [S]
    rw [Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply x)
  exact he ▸ hh

end BinaryLinear.Affine.ThreeLocal
