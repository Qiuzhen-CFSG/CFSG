module

public import Theory.SpecificGroups.MacWilliams.HallJankoFrame
public import Theory.SpecificGroups.MacWilliams.SylowPresentations
public import Theory.SpecificGroups.MacWilliams.HallJankoActionConstruction
public import Theory.SpecificGroups.MacWilliams.HallJankoLiftNormalization
import Mathlib.Tactic

/-!
# Hall–Janko coordinates from an extension frame

The tuple `(t,u,v,b,u*a,a²,b²)` in a normalized action frame satisfies the
seven-generator Hall–Janko presentation and generates the ambient group.
The proof collects words in the order `a,b,u,v,t`, using the frame's action
and lift equations, and checks all seven squares and twenty-one commutators.
Generation follows by recovering `a` from `u` and `u*a`.

This is the coordinate calculation for Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3(a), printed p.386, citing MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3. The intrinsic existence theorem combines
the action construction and lift normalization over a supplied C₄-square base.
-/

namespace MacWilliamsSylow.HallJankoActionFrame

variable {P : Type*} [Group P] {D W B : Subgroup P}

private theorem inv_of_four (a : P) (h : a ^ 4 = 1) : a⁻¹ = a * a * a := by
  calc
    a⁻¹ = a⁻¹ * a ^ 4 := by rw [h, mul_one]
    _ = a * a * a := by
      group
      simp [pow_succ]

set_option maxHeartbeats 2000000 in
/-- All power and right-commutator relations hold in the chosen coordinates. -/
public theorem relations (f : HallJankoActionFrame D W B) (h : f.LiftRelations) :
    Relations hallJankoTable f.tuple := by
  have ia := inv_of_four f.a f.a_four
  have ib := inv_of_four f.b f.b_four
  have iu : f.u⁻¹ = f.u := (inv_eq_iff_mul_eq_one.mpr f.u_two)
  have iv : f.v⁻¹ = f.v := (inv_eq_iff_mul_eq_one.mpr f.v_two)
  have it : f.t⁻¹ = f.t := (inv_eq_iff_mul_eq_one.mpr h.t_two)
  have a4 (x : P) : f.a * (f.a * (f.a * (f.a * x))) = x := by
    have hh := congrArg (fun z : P => z * x) f.a_four
    simpa [pow_succ, mul_assoc] using hh
  have b4 (x : P) : f.b * (f.b * (f.b * (f.b * x))) = x := by
    have hh := congrArg (fun z : P => z * x) f.b_four
    simpa [pow_succ, mul_assoc] using hh
  have u2 (x : P) : f.u * (f.u * x) = x := by rw [← mul_assoc, f.u_two, one_mul]
  have v2 (x : P) : f.v * (f.v * x) = x := by rw [← mul_assoc, f.v_two, one_mul]
  have ba (x : P) : f.b * (f.a * x) = f.a * (f.b * x) := by rw [← mul_assoc, f.ba, mul_assoc]
  have ua (x : P) : f.u * (f.a * x) = f.a * (f.a * (f.a * (f.b * (f.b * (f.u * x))))) := by
    simpa [ia, pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.ua
  have ub (x : P) : f.u * (f.b * x) = f.b * (f.b * (f.b * (f.u * x))) := by
    simpa [ib, mul_assoc] using congrArg (fun z : P => z * x) f.ub
  have va (x : P) : f.v * (f.a * x) = f.a * (f.b * (f.b * (f.v * x))) := by
    simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.va
  have vb (x : P) : f.v * (f.b * x) = f.a * (f.a * (f.b * (f.v * x))) := by
    simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.vb
  have vu (x : P) : f.v * (f.u * x) = f.u * (f.v * x) := by rw [← mul_assoc, f.vu, mul_assoc]
  have ta (x : P) : f.t * (f.a * x) = f.a * (f.b * (f.t * x)) := by
    simpa [mul_assoc] using congrArg (fun z : P => z * x) f.ta
  have tb (x : P) : f.t * (f.b * x) = f.b * (f.b * (f.b * (f.t * x))) := by
    simpa [ib, mul_assoc] using congrArg (fun z : P => z * x) f.tb
  have a4' : f.a * (f.a * (f.a * f.a)) = 1 := by simpa [pow_succ, mul_assoc] using f.a_four
  have b4' : f.b * (f.b * (f.b * f.b)) = 1 := by simpa [pow_succ, mul_assoc] using f.b_four
  constructor
  · intro i
    fin_cases i <;>
      simp [tuple, hallJankoTable, word, pow_succ, mul_assoc, ia,
        a4, ba, ua, ub, a4', b4', f.u_two, f.v_two, h.t_two, f.ba, f.ua]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;>
      simp [tuple, hallJankoTable, word, rightComm, pow_succ, mul_inv_rev, ia, ib, iu, iv, it,
        mul_assoc, a4, b4, u2, v2, ba, ua, ub, va, vb, vu, ta, tb,
        a4', b4', f.u_two, f.v_two, h.t_two,
        f.ba, f.ua, f.ub, f.va, f.vb, f.vu, f.ta, f.tb, h.tu, h.tv]

/-- The coordinate tuple generates whenever the extension frame generates. -/
public theorem tuple_closure (f : HallJankoActionFrame D W B) :
    Subgroup.closure (Set.range f.tuple) = ⊤ := by
  let H := Subgroup.closure (Set.range f.tuple)
  have hx (i : Fin 7) : f.tuple i ∈ H := Subgroup.subset_closure ⟨i, rfl⟩
  have hu : f.u ∈ H := hx 1
  have ha : f.a ∈ H := by
    have hh := H.mul_mem hu (hx 4)
    simpa only [tuple, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
      ← mul_assoc, f.u_two, one_mul] using hh
  apply top_unique
  rw [← f.generate]
  apply (Subgroup.closure_le _).mpr
  intro x hx'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
  rcases hx' with rfl | rfl | rfl | rfl | rfl
  · exact ha
  · exact hx 3
  · exact hu
  · exact hx 2
  · exact hx 0

/-- A normalized frame supplies the exact generating tuple for recognition. -/
public theorem exists_generators (f : HallJankoActionFrame D W B) (h : f.LiftRelations) :
    ∃ x : Fin 7 → P, Relations hallJankoTable x ∧ Subgroup.closure (Set.range x) = ⊤ :=
  ⟨f.tuple, f.relations h, f.tuple_closure⟩

end MacWilliamsSylow.HallJankoActionFrame

namespace MacWilliamsSylow

/-- A self-centralizing normal C₄-square base in the intrinsic order-128
branch supplies the exact Hall–Janko generating tuple. The elementary sixteen
may be replaced during the action construction; no containment of the marked
four in the original sixteen is assumed. -/
public theorem exists_hallJanko_generators_of_c4_square_base
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4) (hWD : W ≤ D)
    (hDC : Subgroup.centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ x : Fin 7 → P, Relations hallJankoTable x ∧
      Subgroup.closure (Set.range x) = ⊤ := by
  obtain ⟨B', hBe, hBc, ⟨f⟩⟩ :=
    exists_action_frame hP hcard hZ hno W D hW hDC hDO hmodel B hB
  let : IsElementaryAbelian 2 B' := hBe
  obtain ⟨f', hf'⟩ := f.exists_normalized hcard hno hW hBc hWD hDC hDO hmodel
  exact f'.exists_generators hf'

end MacWilliamsSylow
