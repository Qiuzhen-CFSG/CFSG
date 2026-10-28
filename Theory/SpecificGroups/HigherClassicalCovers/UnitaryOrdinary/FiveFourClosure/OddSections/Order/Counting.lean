module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Counting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Structural counting of isotropic vectors over the field of order sixteen

For two coordinates write `a = x + y`. If `a = 0`, their norms cancel,
leaving sixteen choices. Otherwise multiplication by the conjugate of `a`
turns the norm equation into a trace equation, with exactly four solutions.
Thus adjoining two coordinates changes the zero count from `Z(n)` to
`16 * Z(n) + 60 * 16^n`. Starting with `Z(1) = 1` gives `Z(5) = 261376`.
No enumeration of vectors or ambient group order is used.

This is the vector-counting step for the unitary line geometry of GLS3,
Section 2.7, used in the order calculation supporting Aschbacher--Smith
I.1.4(4), printed p.408 of `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- The diagonal Hermitian value, using the stored involution in any dimension. -/
def normSum {n : ℕ} (v : Fin n → F) : F := ∑ i, J.conj (v i) * v i

omit [CharP F 2] in
private theorem fixed_normSum {n : ℕ} (v : Fin n → F) :
    J.conj (normSum J v) = normSum J v := by
  unfold normSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, J.conj_involutive, mul_comm]

private theorem trace_card [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (b : F) (hb : J.conj b = b) :
    Nat.card {x : F // x + J.conj x = b} = 4 := by
  obtain ⟨c, hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (Theory.SpecificGroups.UnitaryFive.fixed_card_four J hcard hconj) b hb
  exact (Nat.card_congr (Theory.SpecificGroups.UnitaryFive.PlaneCore.traceFiberEquivFixed
    J b c hc)).trans (Theory.SpecificGroups.UnitaryFive.fixed_card_four J hcard hconj)

private theorem pair_eq (a b t : F) :
    J.conj (a + b) * (a + b) + J.conj b * b + t =
      (J.conj a * b + J.conj (J.conj a * b)) + (J.conj a * a + t) := by
  rw [map_add, map_mul, J.conj_involutive]
  have hz : J.conj b * b + J.conj b * b = 0 := CharTwo.add_self_eq_zero _
  linear_combination hz

private theorem pair_fiber_card [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (a t : F) (ha : a ≠ 0)
    (ht : J.conj t = t) :
    Nat.card {b : F // J.conj (a+b)*(a+b) + J.conj b*b + t = 0} = 4 := by
  let e : F ≃ F := Equiv.mulLeft₀ (J.conj a) ((map_ne_zero J.conj).mpr ha)
  have he (b : F) :
      J.conj (a+b)*(a+b) + J.conj b*b + t = 0 ↔
      e b + J.conj (e b) = -(J.conj a*a + t) := by
    rw [pair_eq, add_eq_zero_iff_eq_neg]
    rfl
  have ee : {b : F // J.conj (a+b)*(a+b) + J.conj b*b + t = 0} ≃
      {x : F // x + J.conj x = -(J.conj a*a + t)} := e.subtypeEquiv he
  rw [Nat.card_congr ee]
  apply trace_card J hcard hconj
  rw [map_neg, map_add, map_mul, J.conj_involutive, ht, mul_comm a]

private def splitPair (n : ℕ) : (Fin (n+2) → F) ≃ F × ((Fin n → F) × F) where
  toFun v := (v 0 + v 1, (fun i => v i.succ.succ), v 1)
  invFun p := Fin.cons (p.1 + p.2.2) (Fin.cons p.2.2 p.2.1)
  left_inv v := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
    · simp [CharTwo.add_cancel_right]
    · simp
    · simp
  right_inv p := by
    rcases p with ⟨a, w, b⟩
    simp [CharTwo.add_cancel_right]

private theorem splitPair_norm (n : ℕ) (v : Fin (n+2) → F) :
    normSum J v = J.conj ((splitPair n v).1 + (splitPair n v).2.2) *
      ((splitPair n v).1 + (splitPair n v).2.2) +
      J.conj (splitPair n v).2.2 * (splitPair n v).2.2 + normSum J (splitPair n v).2.1 := by
  simp only [splitPair, Equiv.coe_fn_mk, CharTwo.add_cancel_right, normSum,
    Fin.sum_univ_succ, Fin.succ_zero_eq_one]
  ring

private theorem zero_fiber_card (n : ℕ) :
    Nat.card {p : (Fin n → F) × F //
      J.conj (0+p.2)*(0+p.2) + J.conj p.2*p.2 + normSum J p.1 = 0} =
      Nat.card {v : Fin n → F // normSum J v = 0} * Nat.card F := by
  let e : {p : (Fin n → F) × F //
      J.conj (0+p.2)*(0+p.2) + J.conj p.2*p.2 + normSum J p.1 = 0} ≃
      {v : Fin n → F // normSum J v = 0} × F :=
    { toFun := fun p => (⟨p.1.1, by simpa [CharTwo.add_self_eq_zero] using p.2⟩, p.1.2)
      invFun := fun p => ⟨(p.1.1, p.2), by simp [CharTwo.add_self_eq_zero, p.1.2]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod]

/-- Adding two Hermitian coordinates gives a trace-fiber recurrence. -/
theorem card_normSum_zero_succ_two [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (n : ℕ) :
    Nat.card {v : Fin (n+2) → F // normSum J v = 0} =
      16 * Nat.card {v : Fin n → F // normSum J v = 0} + 60 * 16^n := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let P := fun (a : F) (p : (Fin n → F) × F) =>
    J.conj (a+p.2)*(a+p.2) + J.conj p.2*p.2 + normSum J p.1 = 0
  have he (v : Fin (n+2) → F) : normSum J v = 0 ↔
      P (splitPair n v).1 (splitPair n v).2 := by rw [splitPair_norm]
  have ee : {v : Fin (n+2) → F // normSum J v = 0} ≃
      {p : F × ((Fin n → F) × F) // P p.1 p.2} := (splitPair n).subtypeEquiv he
  rw [Nat.card_congr ee,
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype P), Nat.card_sigma]
  have hc (a : F) : Nat.card {p // P a p} =
      if a = 0 then Nat.card {v : Fin n → F // normSum J v = 0} * 16
      else 16^n * 4 := by
    split_ifs with ha
    · subst a
      exact (zero_fiber_card J n).trans (by rw [hcard])
    · rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun w b => P a (w,b))),
        Nat.card_sigma]
      simp only [P, pair_fiber_card J hcard hconj a _ ha (fixed_normSum J _),
        Finset.sum_const, Finset.card_univ, smul_eq_mul]
      rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin, hcard]
  simp_rw [hc]
  have hz : (Finset.univ.filter (fun a : F => a = 0)).card = 1 := by
    have heq : Finset.univ.filter (fun a : F => a = 0) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact (congrArg Finset.card heq).trans (Finset.card_singleton _)
  have hn : (Finset.univ.filter (fun a : F => ¬ a = 0)).card = 15 := by
    simp [Finset.filter_ne', ← Nat.card_eq_fintype_card, hcard]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hz, hn]
  simp only [smul_eq_mul]
  ring

/-- There are 261376 isotropic vectors, including zero. -/
theorem card_normSum_zero_five [Finite F] (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    Nat.card {v : Fin 5 → F // normSum J v = 0} = 261376 := by
  have hbase : Nat.card {v : Fin 1 → F // normSum J v = 0} = 1 := by
    have he : {v : Fin 1 → F | normSum J v = 0} = {0} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, normSum, Fin.sum_univ_one]
      rw [mul_eq_zero, map_eq_zero]
      simp only [or_self]
      exact ⟨fun h => funext fun i => by fin_cases i; exact h, fun h => congrFun h 0⟩
    exact (Nat.card_congr (Equiv.setCongr he)).trans (by simp)
  have h3 := card_normSum_zero_succ_two J hcard hconj 1
  have h5 := card_normSum_zero_succ_two J hcard hconj 3
  rw [hbase] at h3
  rw [h3] at h5
  norm_num at h5
  exact h5
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order
