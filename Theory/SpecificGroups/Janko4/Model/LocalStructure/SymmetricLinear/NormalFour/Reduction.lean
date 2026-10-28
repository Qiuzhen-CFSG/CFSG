module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

/-!
# A small matrix commutant excludes normal four-groups in J₄ max4

A normal subgroup of order four centralizes each element whose order divides
35: its permutation action has order dividing 24. The literal words xy and yx
are conjugate. If their common matrix commutant is detected by two binary
entries, a normal four-group would exhaust the four possible pairs, including
the pair that forces its matrix to vanish. Invertibility gives a contradiction.

The numerical order and commutant certificates are supplied in descendants.
No quotient shape, ambient simplicity, or universal pair placement is assumed.
The cyclic-row lemma is the algebraic interface for the finite certificates.

Source: Aschbacher–Smith, 15.3.43, printed p.1140; GLS3 Table 5.3i.
The literal ATLAS program and its attribution are retained in
`SymmetricLinear/Model.lean` and its `Model/source/` directory.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.NormalFour
open Matrix

/-- First output of the literal ATLAS max4 program. -/
def first : max4Subgroup :=
  ⟨(max4Program a b).1, Subgroup.subset_closure (by simp)⟩
/-- Second output of the literal ATLAS max4 program. -/
def second : max4Subgroup :=
  ⟨(max4Program a b).2, Subgroup.subset_closure (by simp)⟩
def cycle : max4Subgroup := first * second
def reverseCycle : max4Subgroup := second * first
abbrev matrix : max4Subgroup →* BinaryMatrix := toMatrix.comp max4Subgroup.subtype

/-- Two entries detect zero in the common matrix commutant of xy and yx. -/
def SmallCommutant : Prop := ∀ T : BinaryMatrix,
  T * matrix cycle = matrix cycle * T →
  T * matrix reverseCycle = matrix reverseCycle * T →
  T 0 0 = 0 → T 0 1 = 0 → T = 0

private theorem normal_four_commutes {G : Type*} [Group G]
    (W : Subgroup G) [Finite W] [W.Normal] (hW : Nat.card W = 4)
    (g : G) (hg : g ^ 35 = 1) (w : W) : Commute g (w : G) := by
  let f : G →* Equiv.Perm W := (MulAut.toPerm W).comp MulAut.conjNormal
  have h35 : f g ^ 35 = 1 := by rw [← map_pow, hg, map_one]
  have h24 : f g ^ 24 = 1 := by
    have h := pow_card_eq_one' (x := f g)
    simpa only [Nat.card_perm, hW, Nat.factorial] using h
  have hf : f g = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨h35, h24⟩
    norm_num at h
    exact h
  have hconj : g * (w : G) * g⁻¹ = w :=
    congrArg Subtype.val (DFunLike.congr_fun hf w)
  exact (mul_inv_eq_iff_eq_mul).mp hconj

private theorem reverseCycle_pow (h : cycle ^ 35 = 1) : reverseCycle ^ 35 = 1 := by
  have he : reverseCycle = MulAut.conj first⁻¹ cycle := by
    change second * first = first⁻¹ * (first * second) * (first⁻¹)⁻¹
    group
  rw [he, ← map_pow, h, map_one]

/-- The actual max4 application of the coprime-action and matrix argument. -/
theorem normal_card_ne_four_of_certificate (hpow : cycle ^ 35 = 1)
    (hcomm : SmallCommutant) (W : Subgroup max4Subgroup) [W.Normal] :
    Nat.card W ≠ 4 := by
  intro hW
  have hc (w : W) : matrix w * matrix cycle = matrix cycle * matrix w :=
    ((normal_four_commutes W hW cycle hpow w).map matrix).eq.symm
  have hd (w : W) : matrix w * matrix reverseCycle = matrix reverseCycle * matrix w :=
    ((normal_four_commutes W hW reverseCycle (reverseCycle_pow hpow) w).map matrix).eq.symm
  let f : W → ZMod 2 × ZMod 2 := fun w => (matrix w 0 0, matrix w 0 1)
  have hi : Function.Injective f := by
    intro u v huv
    have hz : matrix u - matrix v = 0 := by
      apply hcomm
      · rw [sub_mul, mul_sub, hc u, hc v]
      · rw [sub_mul, mul_sub, hd u, hd v]
      · exact sub_eq_zero.mpr (congrArg Prod.fst huv)
      · exact sub_eq_zero.mpr (congrArg Prod.snd huv)
    exact Subtype.ext (toMatrix_injective (sub_eq_zero.mp hz) |> Subtype.ext)
  have hcard : Nat.card W = Nat.card (ZMod 2 × ZMod 2) := by
    rw [hW, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨w, hw⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, hcard⟩).2 (0, 0)
  have hz : matrix w = 0 := hcomm _ (hc w) (hd w)
    (congrArg Prod.fst hw) (congrArg Prod.snd hw)
  have hunit : IsUnit (matrix w) := (toAmbient (w : max4Subgroup)).isUnit
  exact hunit.ne_zero hz

/-- Row reconstruction from a cyclic basis and an annihilator. -/
theorem zero_of_cyclic_annihilator
    {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (o p : n) (C D : Matrix n n K) (W : n → Matrix n n K)
    (Q Qi R P U : Matrix n n K) (z : n → K)
    (hQ : ∀ i, Q i = W i o) (hQi : Qi * Q = 1)
    (hW : ∀ T : Matrix n n K, T * C = C * T → T * D = D * T →
      ∀ i, T * W i = W i * T)
    (hR : ∀ T : Matrix n n K, T * C = C * T → T * D = D * T →
      T * R = R * T)
    (hR0 : R o = 0) (hRU : R * U = P)
    (hP : P = 1 + vecMulVec (Pi.single o 1) ((1 : Matrix n n K) o) +
      vecMulVec (Pi.single p 1) z)
    (T : Matrix n n K) (hTC : T * C = C * T) (hTD : T * D = D * T)
    (h00 : T o o = 0) (h01 : T o p = 0) : T = 0 := by
  have hzero : T o ᵥ* R = 0 := by
    rw [← mul_apply_eq_vecMul, hR T hTC hTD, mul_apply_eq_vecMul, hR0, zero_vecMul]
  have hp : T o ᵥ* P = 0 := by
    rw [← hRU, ← vecMul_vecMul, hzero, zero_vecMul]
  rw [hP, vecMul_add, vecMul_add, vecMul_one, vecMul_vecMulVec,
    vecMul_vecMulVec, dotProduct_single_one, dotProduct_single_one,
    h00, h01, zero_smul, zero_smul, add_zero, add_zero] at hp
  have hQT : Q * T = 0 := by
    funext i
    rw [mul_apply_eq_vecMul, hQ, ← mul_apply_eq_vecMul,
      ← hW T hTC hTD i, mul_apply_eq_vecMul, hp, zero_vecMul]
    rfl
  calc
    T = (Qi * Q) * T := by rw [hQi, one_mul]
    _ = Qi * (Q * T) := mul_assoc _ _ _
    _ = 0 := by rw [hQT, mul_zero]
end Janko4.LocalStructure.SymmetricLinear.NormalFour
