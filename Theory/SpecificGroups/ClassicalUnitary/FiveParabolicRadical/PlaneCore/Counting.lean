module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Parameters
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
import Mathlib.Tactic.Ring

/-!
# Counting the unitary-five plane-unipotent parameters

Over a field of sixteen elements with fourth-power conjugation, the fixed
field has four elements. Trace surjectivity and translation by a solution
identify each diagonal trace fiber with that fixed field. Once the two
vector coordinates and the two diagonal entries are chosen, the upper
off-diagonal entry is free and determines the lower entry. An explicit
equivalence therefore gives `16² · 4² · 16 = 2¹⁶` parameters.

The equivalence in `PlaneCore.Matrices` transfers this order to the concrete
projective unipotent subgroup. Identifying that subgroup with the canonical
two-core remains a separate parabolic-structure assertion.

Source: the plane-parabolic order calculation underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp. 263--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- Translation by one solution identifies a trace fiber with the fixed field. -/
def traceFiberEquivFixed (b c : F) (hc : c + J.conj c = b) :
    {z : F // z + J.conj z = b} ≃ {z : F // J.conj z = z} where
  toFun z := ⟨z.val + c, by
    apply CharTwo.add_eq_zero.mp
    calc
      _ = (z.val + J.conj z.val) + (c + J.conj c) := by rw [map_add]; ring
      _ = 0 := by rw [z.property, hc, CharTwo.add_self_eq_zero]⟩
  invFun z := ⟨z.val + c, by
    calc
      _ = (z.val + J.conj z.val) + (c + J.conj c) := by rw [map_add]; ring
      _ = b := by rw [z.property, CharTwo.add_self_eq_zero, hc, zero_add]⟩
  left_inv z := by apply Subtype.ext; exact CharTwo.add_cancel_right z.val c
  right_inv z := by apply Subtype.ext; exact CharTwo.add_cancel_right z.val c

/-- Each diagonal equation has four solutions. -/
theorem traceFiber_card [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ a, J.conj a = a ^ 4) (a : F) :
    Nat.card {c : F // c + J.conj c = a * J.conj a} = 4 := by
  have hfixed := fixed_card_four J hcard hconj
  obtain ⟨c, hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard hfixed (a * J.conj a) (by rw [map_mul, J.conj_involutive, mul_comm])
  exact (Nat.card_congr (traceFiberEquivFixed J _ c hc)).trans hfixed

/-- The two diagonal trace fibers and the free upper off-diagonal entry
parametrize every matrix satisfying the Hermitian relation. -/
def Parameters.coordinateEquiv : Parameters J ≃
    Σ x : Fin 2 → F, (∀ i, {c : F // c + J.conj c = x i * J.conj (x i)}) × F where
  toFun u := ⟨u.x, (fun i => ⟨u.z i i, u.relation i i⟩), u.z 0 1⟩
  invFun u :=
    { x := u.1
      z := !![u.2.1 0, u.2.2; u.1 1 * J.conj (u.1 0) + J.conj u.2.2, u.2.1 1]
      relation := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact (u.2.1 0).property
        · dsimp
          rw [map_add, map_mul, J.conj_involutive, J.conj_involutive]
          rw [add_comm (J.conj (u.1 1) * u.1 0), CharTwo.add_cancel_left, mul_comm]
        · dsimp
          rw [CharTwo.add_cancel_right]
        · exact (u.2.1 1).property }
  left_inv u := by
    apply Parameters.ext
    · rfl
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact (CharTwo.add_eq_iff_eq_add.mp (u.relation 1 0)).symm
    · rfl
  right_inv u := by
    rcases u with ⟨x, d, b⟩
    apply congrArg (Sigma.mk x)
    apply Prod.ext
    · funext i
      apply Subtype.ext
      fin_cases i <;> rfl
    · rfl

/-- The plane-unipotent parameter group over the field of order sixteen
has order `16² · 4² · 16 = 2¹⁶`. -/
theorem parameters_card [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ a, J.conj a = a ^ 4) : Nat.card (Parameters J) = 2 ^ 16 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_congr (Parameters.coordinateEquiv J), Nat.card_sigma]
  simp only [Nat.card_prod, Nat.card_pi, traceFiber_card J hcard hconj,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard,
    Finset.sum_const, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, Nat.card_fun, hcard, Nat.card_fin]
  norm_num

end Theory.SpecificGroups.UnitaryFive.PlaneCore
