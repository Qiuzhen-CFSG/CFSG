module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum

/-!
# Reconstructing point adjacency from opposition in an octagon of order (2,4)

The four point-distance recurrences imply an explicit square for the opposition
matrix. Its five coefficients are distinct; the coefficient 512 identifies
adjacency. Every permutation preserving opposition preserves these common-
opposite counts, and hence preserves adjacency. The geometric producer in the
adjacent modules derives the recurrences from girth, diameter and valences.

Source: the opposition reconstruction in Aschbacher–Smith J.5.6–12.
-/

public section
namespace SimpleGraph.OctagonOpposition
variable {R : Type*} [Ring R] [IsAddTorsionFree R]

theorem opposition_square (X D₂ D₃ D₄ : R)
    (h₁ : X * X = 10 + X + D₂)
    (h₂ : X * D₂ = 8 * X + D₂ + D₃)
    (h₃ : X * D₃ = 8 * D₂ + D₃ + 5 * D₄)
    (h₄ : X * D₄ = 8 * D₃ + 5 * D₄) :
    D₄ * D₄ = 1024 + 512*X + 640*D₂ + 576*D₃ + 608*D₄ := by
  have hd₂ : D₂ = X^2-X-10 := by
    calc
      D₂ = (X*X)-X-10 := by rw [h₁]; noncomm_ring
      _ = _ := by noncomm_ring
  have hd₃ : D₃ = X^3-2*X^2-17*X+10 := by
    calc
      D₃ = X*D₂-8*X-D₂ := by rw [h₂]; noncomm_ring
      _ = _ := by rw [hd₂]; noncomm_ring
  have hd₄ : 5*D₄ = X^4-3*X^3-23*X^2+35*X+70 := by
    calc
      5*D₄ = X*D₃-8*D₂-D₃ := by rw [h₃]; noncomm_ring
      _ = _ := by rw [hd₃,hd₂]; noncomm_ring; norm_num
  have hp₂ : X^2*D₄ = 64*D₂+48*D₃+65*D₄ := by
    calc
      X^2*D₄ = 8*(X*D₃)+5*(X*D₄) := by rw [pow_two,mul_assoc]; nth_rewrite 1 [h₄]; noncomm_ring
      _ = _ := by rw [h₃,h₄]; noncomm_ring
  have hp₃ : X^3*D₄ = 512*X+448*D₂+632*D₃+565*D₄ := by
    calc
      X^3*D₄ = 64*(X*D₂)+48*(X*D₃)+65*(X*D₄) := by
        rw [show X^3*D₄ = X*(X^2*D₄) by noncomm_ring,hp₂]
        noncomm_ring
      _ = _ := by rw [h₂,h₃,h₄]; noncomm_ring
  have hp₄ : X^4*D₄ = 5120+4096*X+6016*D₂+5600*D₃+5985*D₄ := by
    calc
      X^4*D₄ = 512*(X*X)+448*(X*D₂)+632*(X*D₃)+565*(X*D₄) := by
        rw [show X^4*D₄ = X*(X^3*D₄) by noncomm_ring,hp₃]
        noncomm_ring
      _ = _ := by rw [h₁,h₂,h₃,h₄]; noncomm_ring; norm_num; noncomm_ring
  have hh : 5*(D₄*D₄) = 5*(1024+512*X+640*D₂+576*D₃+608*D₄) := by
    calc
      5*(D₄*D₄) = (5*D₄)*D₄ := by noncomm_ring
      _ = (X^4-3*X^3-23*X^2+35*X+70)*D₄ := by rw [hd₄]
      _ = X^4*D₄-3*(X^3*D₄)-23*(X^2*D₄)+35*(X*D₄)+70*D₄ := by noncomm_ring
      _ = _ := by rw [hp₄,hp₃,hp₂,h₄]; noncomm_ring; norm_num; noncomm_ring
  apply nsmul_right_injective (by decide : (5:ℕ)≠0)
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hh

end SimpleGraph.OctagonOpposition

namespace SimpleGraph.OctagonOpposition
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] def distanceMatrix (d : V → V → Fin 5) (i : Fin 5) : Matrix V V ℤ :=
  fun u v => if d u v=i then 1 else 0

structure Recurrence (d : V → V → Fin 5) : Prop where
  one : distanceMatrix d 1 * distanceMatrix d 1 = 10 + distanceMatrix d 1 + distanceMatrix d 2
  two : distanceMatrix d 1 * distanceMatrix d 2 = 8*distanceMatrix d 1 + distanceMatrix d 2 + distanceMatrix d 3
  three : distanceMatrix d 1 * distanceMatrix d 3 = 8*distanceMatrix d 2 + distanceMatrix d 3 + 5*distanceMatrix d 4
  four : distanceMatrix d 1 * distanceMatrix d 4 = 8*distanceMatrix d 3 + 5*distanceMatrix d 4

private theorem scalar_apply (n : ℕ) [n.AtLeastTwo] (M : Matrix V V ℤ) (u v : V) :
    ((ofNat(n) : Matrix V V ℤ) * M) u v = (ofNat(n) : ℤ) * M u v := by
  change (((n : Matrix V V ℤ) * M) u v) = (n : ℤ) * M u v
  rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]

theorem square_value (d : V → V → Fin 5) (hzero : ∀ u v, d u v=0 ↔ u=v)
    (h : Recurrence d) (u v : V) :
    (distanceMatrix d 4 * distanceMatrix d 4) u v =
      ![1024,512,640,576,608] (d u v) := by
  have : IsAddTorsionFree (Matrix V V ℤ) := by
    constructor
    intro n hn M N he
    ext i j
    have hh := congrFun (congrFun he i) j
    change n • M i j = n • N i j at hh
    exact nsmul_right_injective hn hh
  have hh := opposition_square (distanceMatrix d 1) (distanceMatrix d 2)
    (distanceMatrix d 3) (distanceMatrix d 4) h.one h.two h.three h.four
  have he := congrFun (congrFun hh u) v
  simp only [Matrix.add_apply, scalar_apply, Matrix.ofNat_apply] at he
  generalize hd : d u v=k
  fin_cases k <;> simpa [distanceMatrix, ← hzero u v, hd] using he

omit [DecidableEq V] in
theorem common_opposition (d : V → V → Fin 5) (hsym : ∀ u v, d u v=d v u)
    (u v : V) :
    (distanceMatrix d 4 * distanceMatrix d 4) u v =
      ((Finset.univ.filter (fun w => d u w=4 ∧ d v w=4)).card : ℤ) := by
  rw [Matrix.mul_apply]
  calc
    ∑ w, distanceMatrix d 4 u w * distanceMatrix d 4 w v =
        ∑ w : V, if d u w=4 ∧ d v w=4 then (1:ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      simp only [distanceMatrix,hsym w v]
      split_ifs <;> simp_all
    _ = _ := Finset.sum_boole _ _

theorem adjacency_from_opposition (d : V → V → Fin 5)
    (hzero : ∀ u v, d u v=0 ↔ u=v) (hsym : ∀ u v, d u v=d v u)
    (h : Recurrence d) (u v : V) :
    d u v=1 ↔ (Finset.univ.filter (fun w => d u w=4 ∧ d v w=4)).card=512 := by
  have he := (common_opposition d hsym u v).symm.trans (square_value d hzero h u v)
  generalize hd : d u v=k at he ⊢
  fin_cases k <;> norm_num at he ⊢ <;> omega

end SimpleGraph.OctagonOpposition

namespace SimpleGraph.OctagonOpposition
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem common_opposition_card_invariant (d : V → V → Fin 5)
    (e : V ≃ V) (h : ∀ u v, d (e u) (e v)=4 ↔ d u v=4) (u v : V) :
    (Finset.univ.filter (fun w => d u w=4 ∧ d v w=4)).card =
      (Finset.univ.filter (fun w => d (e u) w=4 ∧ d (e v) w=4)).card := by
  apply Finset.card_bij (fun w _ => e w)
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    exact ⟨(h u w).mpr hw.1,(h v w).mpr hw.2⟩
  · intro a ha b hb he
    exact e.injective he
  · intro b hb
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
    exact ⟨(h u (e.symm b)).mp (by simpa using hb.1),
      (h v (e.symm b)).mp (by simpa using hb.2)⟩

theorem adjacency_invariant_of_opposition (d : V → V → Fin 5)
    (hzero : ∀ u v, d u v=0 ↔ u=v) (hsym : ∀ u v, d u v=d v u)
    (hr : Recurrence d) (e : V ≃ V)
    (h : ∀ u v, d (e u) (e v)=4 ↔ d u v=4) (u v : V) :
    d (e u) (e v)=1 ↔ d u v=1 := by
  rw [adjacency_from_opposition d hzero hsym hr,
    adjacency_from_opposition d hzero hsym hr,
    ←common_opposition_card_invariant d e h u v]

end SimpleGraph.OctagonOpposition
