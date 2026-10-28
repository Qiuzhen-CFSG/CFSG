module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Transfer
public import Theory.GroupTheory.CosetWordCertificate.Tietze
/-!
# A checked calculus for the literal HS Schreier reduction

Rotating a word preserves the assertion that its evaluation is one. Multiplying
by an established relation and freely cancelling preserves that assertion in
both directions. The checker records these elementary steps with strictly
smaller dependency indices. Thus candidate Tietze data can be interpreted in
the original carrier without assuming any finite quotient faithful.

Source: the ATLAS HSG1-P1.M Schreier presentation and the candidate reduction
in `../source/`. Certificate provenance is recorded in `source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.ValidityCertificate
open Subgroup.CosetWordCertificate

def reduceStack {α : Type*} [DecidableEq α] : Word α → Word α → Word α
  | [], stack => stack.reverse
  | a :: w, [] => reduceStack w [a]
  | a :: w, b :: stack =>
      if a = (b.1, !b.2) then reduceStack w stack else reduceStack w (a :: b :: stack)

theorem eval_reduceStack {α G : Type*} [Group G] [DecidableEq α]
    (g : α → G) (w stack : Word α) :
    eval g (reduceStack w stack) = eval g stack.reverse * eval g w := by
  induction w generalizing stack with
  | nil => simp [reduceStack]
  | cons a w ih =>
    cases stack with
    | nil => simpa [reduceStack, eval_cons] using ih [a]
    | cons b stack =>
      simp only [reduceStack]
      split
      · rename_i h
        subst a
        rw [ih]
        rcases b with ⟨k, sign⟩
        cases sign <;> simp [eval_append, eval_cons, mul_assoc]
      · rw [ih]
        simp [eval_append, eval_cons, mul_assoc]

def fastReduce {α : Type*} [DecidableEq α] (w : Word α) : Word α := reduceStack w []

theorem eval_fastReduce {α G : Type*} [Group G] [DecidableEq α]
    (g : α → G) (w : Word α) : eval g (fastReduce w) = eval g w := by
  simpa [fastReduce] using eval_reduceStack g w []

def rotate {α : Type*} (w : Word α) (n : Nat) : Word α := w.drop n ++ w.take n

theorem rotate_one_iff {α G : Type*} [Group G] (g : α → G) (w : Word α) (n : Nat) :
    eval g (rotate w n) = 1 ↔ eval g w = 1 := by
  rw [rotate, eval_append, mul_eq_one_comm, ← eval_append, List.take_append_drop]

def transform {α : Type*} [DecidableEq α] (w r : Word α)
    (a b c : Nat) (positive : Bool) : Word α :=
  fastReduce (rotate (fastReduce (rotate w a ++ rotate (if positive then r else FreeGroup.invRev r) b)) c)

theorem transform_one_iff {α G : Type*} [Group G] [DecidableEq α]
    (g : α → G) (w r : Word α) (a b c : Nat) (positive : Bool)
    (hr : eval g r = 1) :
    eval g (transform w r a b c positive) = 1 ↔ eval g w = 1 := by
  have hi : eval g (if positive then r else FreeGroup.invRev r) = 1 := by
    cases positive <;> simp [hr, eval_invRev]
  have h := (rotate_one_iff g _ b).mpr hi
  rw [transform, eval_fastReduce, rotate_one_iff, eval_fastReduce, eval_append, h, mul_one,
    rotate_one_iff]

abbrev W := Word (Fin 101)

def rawRelator (r : Nat) : W := Schreier.relatorWord
  ⟨(r / 13) % 100, Nat.mod_lt _ (by decide)⟩ ⟨r % 13, Nat.mod_lt _ (by decide)⟩

theorem rawRelator_valid (r : Nat) : eval localGenerator (rawRelator r) = 1 :=
  local_relator _ _

structure Instruction where
  kind : Nat
  p : Nat := 0
  q : Nat := 0
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0
  positive : Bool := true

def check (words : Nat → W) (ops : Nat → Instruction) (n : Nat) : Bool :=
  match ops n with
  | ⟨kind, p, q, a, b, c, positive⟩ =>
    if kind = 0 then decide (words n = [])
    else if kind = 1 then
      decide (fastReduce (rotate (fastReduce (rawRelator p)) c) = words n)
    else (p < n && q < n) &&
      if kind = 2 then
        decide (transform (words p) (words q) a b c positive = words n)
      else
        decide (transform (words n) (words q) a b c positive = words p)

theorem check_sound (words : Nat → W) (ops : Nat → Instruction) (n : Nat)
    (ih : ∀ k, k < n → eval localGenerator (words k) = 1)
    (hc : check words ops n = true) : eval localGenerator (words n) = 1 := by
  cases ho : ops n with
  | mk kind p q a b c positive =>
    simp only [check, ho] at hc
    split at hc
    · have hw : words n = [] := of_decide_eq_true hc
      rw [hw, eval_nil]
    · split at hc
      · have hw := of_decide_eq_true hc
        rw [← hw, eval_fastReduce]
        apply (rotate_one_iff _ _ _).mpr
        rw [eval_fastReduce]
        exact rawRelator_valid _
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hp := ih p hc.1.1
        have hq := ih q hc.1.2
        split at hc
        · have hw := of_decide_eq_true hc.2
          rw [← hw]
          exact (transform_one_iff _ _ _ _ _ _ _ hq).mpr hp
        · have hw := of_decide_eq_true hc.2
          apply (transform_one_iff _ _ _ a b c positive hq).mp
          rw [hw]
          exact hp

theorem sound (words : Nat → W) (ops : Nat → Instruction) (bound : Nat)
    (hc : ∀ n, n < bound → check words ops n = true) :
    ∀ n, n < bound → eval localGenerator (words n) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    exact check_sound words ops n (fun k hk => ih k hk (hk.trans hn)) (hc n hn)


/-- A supplied cut removes a freely cancelling conjugator and chooses a cyclic start. -/
def normalize {α : Type*} [DecidableEq α] (w : Word α) (cut : Nat) : Word α :=
  fastReduce (rotate (fastReduce w) cut)

theorem normalize_one_iff {α G : Type*} [Group G] [DecidableEq α]
    (g : α → G) (w : Word α) (cut : Nat) :
    eval g (normalize w cut) = 1 ↔ eval g w = 1 := by
  rw [normalize, eval_fastReduce, rotate_one_iff, eval_fastReduce]

/-- Balanced assembly of checked intervals. -/
theorem checks_join (p : Nat → Bool) (start middle stop : Nat)
    (hl : ∀ n, start ≤ n → n < middle → p n = true)
    (hr : ∀ n, middle ≤ n → n < stop → p n = true) :
    ∀ n, start ≤ n → n < stop → p n = true := by
  intro n hlo hhi
  by_cases h : n < middle
  · exact hl n hlo h
  · exact hr n (by omega) hhi

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced.ValidityCertificate
