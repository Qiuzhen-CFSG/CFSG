module

public import Theory.SpecificGroups.MacWilliams.HallJankoLiftAlgebra
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

/-!
# Existence of Hall–Janko lift parameters

The marked generators identify the base with a C₄-square: their fourth-power
relations give a surjective coordinate map, and the given model proves its
injectivity by cardinality. Conjugation by the three lifts acts on these
coordinates by `U(i,j)=(-i,2i-j)`, `V(i,j)=(i+2j,2i+j)`, and
`T(i,j)=(i,i-j)`.

The three lift defects lie in the base by `lift_defects_mem_base`. Applying
conjugation by `t` to the involution and commutation relations, and squaring
that conjugation, gives six consistency equations. A kernel-checked finite
calculation gives the 32 parameter forms recorded by `LiftParameters`.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

set_option linter.unusedSimpArgs false

namespace MacWilliamsSylow.HallJankoActionFrame
variable {P : Type*} [Group P] {D W B : Subgroup P}
private theorem inv_of_four (a : P) (h : a ^ 4 = 1) : a⁻¹ = a * a * a := by
  calc
    a⁻¹ = a⁻¹ * a ^ 4 := by rw [h, mul_one]
    _ = a * a * a := by group; simp [pow_succ]
private theorem collect_a4 (f : HallJankoActionFrame D W B) (x : P) :
    f.a * (f.a * (f.a * (f.a * x))) = x := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.a_four
private theorem collect_b4 (f : HallJankoActionFrame D W B) (x : P) :
    f.b * (f.b * (f.b * (f.b * x))) = x := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.b_four
private theorem collect_ba (f : HallJankoActionFrame D W B) (x : P) :
    f.b * (f.a * x) = f.a * (f.b * x) := by rw [← mul_assoc, f.ba, mul_assoc]
private theorem collect_ua (f : HallJankoActionFrame D W B) (x : P) :
    f.u * (f.a * x) = f.a * (f.a * (f.a * (f.b * (f.b * (f.u * x))))) := by
  simpa [inv_of_four f.a f.a_four, pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.ua
private theorem collect_ub (f : HallJankoActionFrame D W B) (x : P) :
    f.u * (f.b * x) = f.b * (f.b * (f.b * (f.u * x))) := by
  simpa [inv_of_four f.b f.b_four, mul_assoc] using congrArg (fun z : P => z * x) f.ub
private theorem collect_va (f : HallJankoActionFrame D W B) (x : P) :
    f.v * (f.a * x) = f.a * (f.b * (f.b * (f.v * x))) := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.va
private theorem collect_vb (f : HallJankoActionFrame D W B) (x : P) :
    f.v * (f.b * x) = f.a * (f.a * (f.b * (f.v * x))) := by
  simpa [pow_succ, mul_assoc] using congrArg (fun z : P => z * x) f.vb
private theorem collect_ta (f : HallJankoActionFrame D W B) (x : P) :
    f.t * (f.a * x) = f.a * (f.b * (f.t * x)) := by
  simpa [mul_assoc] using congrArg (fun z : P => z * x) f.ta
private theorem collect_tb (f : HallJankoActionFrame D W B) (x : P) :
    f.t * (f.b * x) = f.b * (f.b * (f.b * (f.t * x))) := by
  simpa [inv_of_four f.b f.b_four, mul_assoc] using congrArg (fun z : P => z * x) f.tb

private abbrev C := ZMod 4 × ZMod 4
private def U (c : C) : C := (-c.1, 2*c.1-c.2)
private def V (c : C) : C := (c.1+2*c.2, 2*c.1+c.2)
private def T (c : C) : C := (c.1, c.1-c.2)
private def coord (f : HallJankoActionFrame D W B) (c : C) : P :=
  f.a ^ c.1.val * f.b ^ c.2.val
private theorem coord_zero (f : HallJankoActionFrame D W B) : coord f 0 = 1 := by
  simp [coord]
private theorem pow_add_val (a : P) (ha : a^4=1) (i j : ZMod 4) :
    a ^ (i+j).val = a^i.val * a^j.val := by
  rw [ZMod.val_add, ← pow_add]
  exact pow_eq_pow_of_modEq (Nat.mod_mod _ _ ) ha
private theorem coord_add (f : HallJankoActionFrame D W B) (c d : C) :
    coord f (c+d) = coord f c * coord f d := by
  simp only [coord, Prod.fst_add, Prod.snd_add,
    pow_add_val _ f.a_four, pow_add_val _ f.b_four]
  have h : Commute f.b f.a := f.ba
  have h' := (h.pow_pow c.2.val d.1.val).eq
  calc
    _ = f.a ^ c.1.val * (f.a ^ d.1.val * f.b ^ c.2.val) * f.b ^ d.2.val := by group
    _ = _ := by rw [← h']; group
private theorem coord_neg (f : HallJankoActionFrame D W B) (c : C) :
    coord f (-c) = (coord f c)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← coord_add, neg_add_cancel, coord_zero]
private theorem coord_mem (f : HallJankoActionFrame D W B) (c : C) : coord f c ∈ D := by
  have ha : f.a ∈ D := by simp only [f.base]; exact Subgroup.subset_closure (by simp)
  have hb : f.b ∈ D := by simp only [f.base]; exact Subgroup.subset_closure (by simp)
  exact D.mul_mem (D.pow_mem ha _) (D.pow_mem hb _)
private theorem coord_surj (f : HallJankoActionFrame D W B) (x : P) (hx : x ∈ D) :
    ∃ c, coord f c = x := by
  let R : Subgroup P :=
    { carrier := Set.range (coord f)
      one_mem' := ⟨0, coord_zero f⟩
      mul_mem' := by rintro x y ⟨c,rfl⟩ ⟨d,rfl⟩; exact ⟨c+d, coord_add f c d⟩
      inv_mem' := by rintro x ⟨c,rfl⟩; exact ⟨-c, coord_neg f c⟩ }
  have h : D ≤ R := by
    rw [f.base]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with rfl | ⟨rfl⟩
    · exact ⟨(1,0), by change f.a ^ 1 * f.b ^ 0 = f.a; simp⟩
    · exact ⟨(0,1), by change f.a ^ 0 * f.b ^ 1 = f.b; simp⟩
  exact h hx
-- Generation and equal finite cardinalities make the coordinates unique.
private theorem coord_inj (f : HallJankoActionFrame D W B)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) :
    Function.Injective (coord f) := by
  let g : C → D := fun c => ⟨coord f c, coord_mem f c⟩
  have hs : Function.Surjective g := by
    intro x
    obtain ⟨c,hc⟩ := coord_surj f x x.property
    exact ⟨c, Subtype.ext hc⟩
  have hc : Nat.card D = Nat.card C := by
    obtain ⟨e⟩ := hmodel
    exact Nat.card_congr e.toEquiv
  have hi := (hs.bijective_of_nat_card_le (le_of_eq hc.symm)).1
  intro c d h
  exact hi (Subtype.ext h)

private theorem coord_u (f : HallJankoActionFrame D W B) (c : C) :
    f.u * coord f c = coord f (U c) * f.u := by
  rcases c with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · change f.u * (f.a ^ 0 * f.b ^ 0) = (f.a ^ 0 * f.b ^ 0) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 0 * f.b ^ 1) = (f.a ^ 0 * f.b ^ 3) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 0 * f.b ^ 2) = (f.a ^ 0 * f.b ^ 2) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 0 * f.b ^ 3) = (f.a ^ 0 * f.b ^ 1) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 1 * f.b ^ 0) = (f.a ^ 3 * f.b ^ 2) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 1 * f.b ^ 1) = (f.a ^ 3 * f.b ^ 1) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 1 * f.b ^ 2) = (f.a ^ 3 * f.b ^ 0) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 1 * f.b ^ 3) = (f.a ^ 3 * f.b ^ 3) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 2 * f.b ^ 0) = (f.a ^ 2 * f.b ^ 0) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 2 * f.b ^ 1) = (f.a ^ 2 * f.b ^ 3) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 2 * f.b ^ 2) = (f.a ^ 2 * f.b ^ 2) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 2 * f.b ^ 3) = (f.a ^ 2 * f.b ^ 1) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 3 * f.b ^ 0) = (f.a ^ 1 * f.b ^ 2) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 3 * f.b ^ 1) = (f.a ^ 1 * f.b ^ 1) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 3 * f.b ^ 2) = (f.a ^ 1 * f.b ^ 0) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.u * (f.a ^ 3 * f.b ^ 3) = (f.a ^ 1 * f.b ^ 3) * f.u
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ua, collect_ub,
      f.ba, f.ua, f.ub, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
private theorem coord_v (f : HallJankoActionFrame D W B) (c : C) :
    f.v * coord f c = coord f (V c) * f.v := by
  rcases c with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · change f.v * (f.a ^ 0 * f.b ^ 0) = (f.a ^ 0 * f.b ^ 0) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 0 * f.b ^ 1) = (f.a ^ 2 * f.b ^ 1) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 0 * f.b ^ 2) = (f.a ^ 0 * f.b ^ 2) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 0 * f.b ^ 3) = (f.a ^ 2 * f.b ^ 3) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 1 * f.b ^ 0) = (f.a ^ 1 * f.b ^ 2) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 1 * f.b ^ 1) = (f.a ^ 3 * f.b ^ 3) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 1 * f.b ^ 2) = (f.a ^ 1 * f.b ^ 0) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 1 * f.b ^ 3) = (f.a ^ 3 * f.b ^ 1) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 2 * f.b ^ 0) = (f.a ^ 2 * f.b ^ 0) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 2 * f.b ^ 1) = (f.a ^ 0 * f.b ^ 1) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 2 * f.b ^ 2) = (f.a ^ 2 * f.b ^ 2) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 2 * f.b ^ 3) = (f.a ^ 0 * f.b ^ 3) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 3 * f.b ^ 0) = (f.a ^ 3 * f.b ^ 2) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 3 * f.b ^ 1) = (f.a ^ 1 * f.b ^ 3) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 3 * f.b ^ 2) = (f.a ^ 3 * f.b ^ 0) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.v * (f.a ^ 3 * f.b ^ 3) = (f.a ^ 1 * f.b ^ 1) * f.v
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_va, collect_vb,
      f.ba, f.va, f.vb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
private theorem coord_t (f : HallJankoActionFrame D W B) (c : C) :
    f.t * coord f c = coord f (T c) * f.t := by
  rcases c with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · change f.t * (f.a ^ 0 * f.b ^ 0) = (f.a ^ 0 * f.b ^ 0) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 0 * f.b ^ 1) = (f.a ^ 0 * f.b ^ 3) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 0 * f.b ^ 2) = (f.a ^ 0 * f.b ^ 2) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 0 * f.b ^ 3) = (f.a ^ 0 * f.b ^ 1) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 1 * f.b ^ 0) = (f.a ^ 1 * f.b ^ 1) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 1 * f.b ^ 1) = (f.a ^ 1 * f.b ^ 0) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 1 * f.b ^ 2) = (f.a ^ 1 * f.b ^ 3) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 1 * f.b ^ 3) = (f.a ^ 1 * f.b ^ 2) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 2 * f.b ^ 0) = (f.a ^ 2 * f.b ^ 2) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 2 * f.b ^ 1) = (f.a ^ 2 * f.b ^ 1) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 2 * f.b ^ 2) = (f.a ^ 2 * f.b ^ 0) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 2 * f.b ^ 3) = (f.a ^ 2 * f.b ^ 3) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 3 * f.b ^ 0) = (f.a ^ 3 * f.b ^ 3) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 3 * f.b ^ 1) = (f.a ^ 3 * f.b ^ 2) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 3 * f.b ^ 2) = (f.a ^ 3 * f.b ^ 1) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]
  · change f.t * (f.a ^ 3 * f.b ^ 3) = (f.a ^ 3 * f.b ^ 0) * f.t
    simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc,
      collect_a4, collect_b4, collect_ba, collect_ta, collect_tb,
      f.ba, f.ta, f.tb, inv_of_four f.a f.a_four, inv_of_four f.b f.b_four]

private theorem push {g a b : P} (h : g*a=b*g) (w : P) :
    g*(a*w)=b*(g*w) := by rw [← mul_assoc, h, mul_assoc]

-- The relations transported by conjugation by t give all six constraints.
private theorem constraints (f : HallJankoActionFrame D W B)
    (hi : Function.Injective (coord f)) (x y z : C)
    (htt : f.t*f.t = coord f x)
    (htu : f.t*f.u = coord f y*f.u*f.t)
    (htv : f.t*f.v = coord f z*f.u*f.v*f.t) :
    T x = x ∧ y + U y = 0 ∧ z + U (V z) = 0 ∧
    y + U z = z + U (V y) ∧
    T y + y = x - U x ∧ T z + y + U z = x - V x := by
  let α := MulAut.conj f.t
  have hc (c : C) : α (coord f c) = coord f (T c) := by
    change f.t * coord f c * f.t⁻¹ = _
    rw [coord_t, mul_inv_cancel_right]
  have hu : α f.u = coord f y * f.u := by
    change f.t * f.u * f.t⁻¹ = _
    rw [htu, mul_inv_cancel_right]
  have hv : α f.v = coord f z * (f.u*f.v) := by
    change f.t * f.v * f.t⁻¹ = _
    rw [htv, mul_inv_cancel_right, mul_assoc]
  have h2 (w : P) : α (α w) = coord f x * w * (coord f x)⁻¹ := by
    change f.t * (f.t*w*f.t⁻¹) * f.t⁻¹ = _
    rw [← htt]
    group
  have huv (c : C) : (f.u*f.v)*coord f c = coord f (U (V c))*(f.u*f.v) := by
    rw [mul_assoc, coord_v, ← mul_assoc, coord_u, mul_assoc]
  have huu (w : P) : f.u*(f.u*w)=w := by rw [← mul_assoc, f.u_two, one_mul]
  have hvu (w : P) : f.v*(f.u*w)=f.u*(f.v*w) := push f.vu w
  have hww : (f.u*f.v)*(f.u*f.v)=1 := by
    simp only [mul_assoc, hvu, huu, f.v_two]
  have hTx : T x = x := by
    apply hi
    rw [← hc, ← htt]
    change f.t*(f.t*f.t)*f.t⁻¹=f.t*f.t
    group
  have hyy : y+U y=0 := by
    apply hi
    have hh := congrArg α f.u_two
    simp only [map_mul, map_one] at hh
    simpa only [map_mul, map_one, hu, coord_add, coord_zero, mul_assoc,
      push (coord_u f y), f.u_two, mul_one] using hh
  have hzz : z+U (V z)=0 := by
    apply hi
    have hh := congrArg α f.v_two
    have he : (coord f z*(f.u*f.v))*(coord f z*(f.u*f.v)) =
        coord f (z+U (V z)) := by
      rw [mul_assoc, push (huv z), hww, mul_one, coord_add]
    simpa only [map_mul, map_one, hv, he, coord_zero] using hh
  have hyz : y+U z=z+U (V y) := by
    apply hi
    apply (mul_right_cancel_iff (a := f.v)).mp
    have hh := congrArg α f.vu.symm
    simp only [map_mul] at hh
    simpa only [map_mul, hu, hv, coord_add, mul_assoc,
      push (coord_u f z), push (coord_v f y), push (coord_u f (V y)),
      huu, hvu, f.vu] using hh
  have hTy : T y+y=x-U x := by
    apply hi
    apply (mul_right_cancel_iff (a := f.u)).mp
    have hh := h2 f.u
    have he : coord f x * f.u * (coord f x)⁻¹ = coord f (x-U x)*f.u := by
      rw [sub_eq_add_neg, coord_add, coord_neg]
      have h := coord_u f x
      have hinv : f.u*(coord f x)⁻¹=(coord f (U x))⁻¹*f.u := by
        have hh := congrArg (fun w : P => (coord f (U x))⁻¹*w*(coord f x)⁻¹) h
        simpa only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using hh.symm
      rw [mul_assoc, hinv, ← mul_assoc]
    simpa only [hu, map_mul, hc, he, coord_add, mul_assoc] using hh
  have hTz : T z+y+U z=x-V x := by
    apply hi
    apply (mul_right_cancel_iff (a := f.v)).mp
    have hh := h2 f.v
    have he : coord f x * f.v * (coord f x)⁻¹ = coord f (x-V x)*f.v := by
      rw [sub_eq_add_neg, coord_add, coord_neg]
      have h := coord_v f x
      have hinv : f.v*(coord f x)⁻¹=(coord f (V x))⁻¹*f.v := by
        have hh := congrArg (fun w : P => (coord f (V x))⁻¹*w*(coord f x)⁻¹) h
        simpa only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using hh.symm
      rw [mul_assoc, hinv, ← mul_assoc]
    simpa only [hv, map_mul, hc, hu, he, coord_add, mul_assoc,
      push (coord_u f z), huu] using hh
  exact ⟨hTx,hyy,hzz,hyz,hTy,hTz⟩

-- The free coordinates are x₂, y₂, and half the even coordinate z₂.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem enumerate : ∀ x y z : C,
    T x = x ∧ y + U y = 0 ∧ z + U (V z) = 0 ∧
    y + U z = z + U (V y) ∧
    T y + y = x - U x ∧ T z + y + U z = x - V x →
    x.1.val = (2*x.2.val)%4 ∧ y.1.val = (2*x.2.val)%4 ∧
    z.1.val = y.2.val ∧ z.2.val = 2*(z.2.val/2) := by decide

/-- Every self-centralizing C₄-square action frame admits the 32-parameter
form of its three remaining lift equations. -/
public theorem nonempty_liftParameters [Finite P] [D.Normal] [IsMulCommutative D]
    (f : HallJankoActionFrame D W B)
    (hDC : Subgroup.centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    : Nonempty f.LiftParameters := by
  obtain ⟨hx,hy,hz⟩ := f.lift_defects_mem_base hDC
  obtain ⟨x,hx⟩ := coord_surj f _ hx
  obtain ⟨y,hy⟩ := coord_surj f _ hy
  obtain ⟨z,hz⟩ := coord_surj f _ hz
  have htu : f.t*f.u=coord f y*f.u*f.t := by rw [hy]; group
  have htv : f.t*f.v=coord f z*f.u*f.v*f.t := by rw [hz]; group
  obtain ⟨hxx,hyy,hzz,hzz'⟩ := enumerate x y z
    (constraints f (coord_inj f hmodel) x y z hx.symm htu htv)
  let r : Fin 4 := ⟨x.2.val, ZMod.val_lt _⟩
  let j : Fin 4 := ⟨y.2.val, ZMod.val_lt _⟩
  let k : Fin 2 := ⟨z.2.val/2, by have h := ZMod.val_lt z.2; omega⟩
  have hp (n : ℕ) : f.a ^ (n%4) = f.a ^ n :=
    pow_eq_pow_of_modEq (Nat.mod_mod _ _) f.a_four
  refine ⟨⟨r,j,k,?_,?_,?_⟩⟩
  · rw [← hx]
    change f.a ^ x.1.val * f.b ^ x.2.val = f.a ^ (2*x.2.val) * f.b ^ x.2.val
    rw [hxx,hp]
  · rw [htu]
    change (f.a ^ y.1.val * f.b ^ y.2.val)*f.u*f.t =
      (f.a ^ (2*x.2.val) * f.b ^ y.2.val)*f.u*f.t
    rw [hyy,hp]
  · rw [htv]
    change (f.a ^ z.1.val * f.b ^ z.2.val)*f.u*f.v*f.t =
      (f.a ^ y.2.val * f.b ^ (2*(z.2.val/2)))*f.u*f.v*f.t
    conv_lhs => rw [hzz,hzz']

end MacWilliamsSylow.HallJankoActionFrame
