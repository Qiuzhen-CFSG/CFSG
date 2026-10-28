module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# The six-coordinate invariant-subspace calculation

The coordinates are the prospective cosets of the ascending words on
`[g9,g11,g13,g14,g15,g17]`, modulo `<g16,g18,g19,g20>`.
This module proves a finite algebra assertion independently of any presentation
comparison: a binary subspace invariant under five displayed displacement maps,
on which the two square coordinates vanish, is either in the displayed kernel
or one of nine explicit subspaces. `AbstractCatalogue` supplies its subgroup
consumer; its word-calculus premises remain separate proof obligations.

The proof uses an exhaustive decision tree with 16 leaves. Every propagation
step is an application of xor closure or one of the five maps; every rejection
uses a nonzero square coordinate or a previously excluded vector. The generator
script chooses proof terms only, and no external computation is trusted.

Source context: Aschbacher–Smith A.3.12, pp.47–48; the literal PC relations in
`SylowNormalEights/PresentationData.lean` and the discovery provenance in
`OutsideKernelOrders/source/README.md`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue

/-- Six binary coordinates, with the first displayed generator in bit zero. -/
abbrev Code := Fin 64

def codeXor (a b : Code) : Code := ⟨Nat.xor a.val b.val % 64, Nat.mod_lt _ (by decide)⟩

def bit (n : Code) (k : ℕ) : ℕ := n.val / 2 ^ k % 2

/-- Displacements for conjugation by g0, g1, g2, g4 and g5, respectively. -/
def displacement (j : Fin 5) (n : Code) : Code :=
  ⟨(![8 * bit n 0 + 32 * ((bit n 0 + bit n 2) % 2),
      8 * bit n 1 + 16 * bit n 2 + 32 * bit n 1,
      32 * ((bit n 0 + bit n 3) % 2),
      32 * bit n 1, 8 * bit n 0] j) % 64, Nat.mod_lt _ (by decide)⟩

/-- The two nontrivial central coordinates of the square. -/
def squareZero (n : Code) : Prop :=
  bit n 0 * bit n 2 = 0 ∧
    (bit n 1 * bit n 4 + bit n 2 * bit n 3) % 2 = 0

instance (n : Code) : Decidable (squareZero n) := inferInstanceAs (Decidable (_ ∧ _))

/-- The kernel section has zero g13- and g15-coordinates. -/
def kernelCode (n : Code) : Prop := bit n 2 = 0 ∧ bit n 4 = 0

instance (n : Code) : Decidable (kernelCode n) := inferInstanceAs (Decidable (_ ∧ _))

/-- Bases matching the nine literal rows of `candidateWords`. -/
def candidateBasis : Fin 9 → List Code :=
  ![[48], [16], [24, 32], [17, 8, 32], [6, 24, 32],
    [16, 32], [4, 16, 32], [8, 16, 32], [1, 8, 16, 32]]

/-- All binary subset sums. Independence is unnecessary for the closure lemma. -/
def codeSpan : List Code → List Code
  | [] => [0]
  | a :: l => codeSpan l ++ (codeSpan l).map (codeXor a)

def candidateCodes (i : Fin 9) : List Code := codeSpan (candidateBasis i)

/-- The exact elementary and invariance conditions used by the finite proof. -/
structure ClosedCoordinates (P : Code → Prop) : Prop where
  zero : P 0
  xor : ∀ a b, P a → P b → P (codeXor a b)
  invariant : ∀ j n, P n → P (displacement j n)
  square : ∀ n, P n → squareZero n

/-- Binary sums of members remain members. -/
theorem codeSpan_mem {P : Code → Prop} (hzero : P 0)
    (hxor : ∀ a b, P a → P b → P (codeXor a b))
    (l : List Code) (hl : ∀ n ∈ l, P n) : ∀ n ∈ codeSpan l, P n := by
  induction l with
  | nil => simpa only [codeSpan, List.mem_singleton] using fun n (h : n = 0) => h ▸ hzero
  | cons a l ih =>
    have ht := ih (fun n hn => hl n (List.mem_cons_of_mem a hn))
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact ht n hn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
      exact hxor a m (hl a List.mem_cons_self) (ht m hm)

private theorem mem_xor {P : Code → Prop} (h : ClosedCoordinates P)
    {a b c : Code} (ha : P a) (hb : P b) (hc : codeXor a b = c) : P c :=
  hc ▸ h.xor a b ha hb

private theorem mem_displacement {P : Code → Prop} (h : ClosedCoordinates P)
    (j : Fin 5) {a b : Code} (ha : P a) (hb : displacement j a = b) : P b :=
  hb ▸ h.invariant j a ha

private theorem not_mem_square {P : Code → Prop} (h : ClosedCoordinates P)
    {a : Code} (ha : ¬ squareZero a) : ¬ P a := fun hp => ha (h.square a hp)

private theorem forall_code (Q : Code → Prop)
    (h0 : Q 0)
    (h1 : Q 1)
    (h2 : Q 2)
    (h3 : Q 3)
    (h4 : Q 4)
    (h5 : Q 5)
    (h6 : Q 6)
    (h7 : Q 7)
    (h8 : Q 8)
    (h9 : Q 9)
    (h10 : Q 10)
    (h11 : Q 11)
    (h12 : Q 12)
    (h13 : Q 13)
    (h14 : Q 14)
    (h15 : Q 15)
    (h16 : Q 16)
    (h17 : Q 17)
    (h18 : Q 18)
    (h19 : Q 19)
    (h20 : Q 20)
    (h21 : Q 21)
    (h22 : Q 22)
    (h23 : Q 23)
    (h24 : Q 24)
    (h25 : Q 25)
    (h26 : Q 26)
    (h27 : Q 27)
    (h28 : Q 28)
    (h29 : Q 29)
    (h30 : Q 30)
    (h31 : Q 31)
    (h32 : Q 32)
    (h33 : Q 33)
    (h34 : Q 34)
    (h35 : Q 35)
    (h36 : Q 36)
    (h37 : Q 37)
    (h38 : Q 38)
    (h39 : Q 39)
    (h40 : Q 40)
    (h41 : Q 41)
    (h42 : Q 42)
    (h43 : Q 43)
    (h44 : Q 44)
    (h45 : Q 45)
    (h46 : Q 46)
    (h47 : Q 47)
    (h48 : Q 48)
    (h49 : Q 49)
    (h50 : Q 50)
    (h51 : Q 51)
    (h52 : Q 52)
    (h53 : Q 53)
    (h54 : Q 54)
    (h55 : Q 55)
    (h56 : Q 56)
    (h57 : Q 57)
    (h58 : Q 58)
    (h59 : Q 59)
    (h60 : Q 60)
    (h61 : Q 61)
    (h62 : Q 62)
    (h63 : Q 63)
    : ∀ n, Q n := by
  intro n
  fin_cases n <;> assumption

/-- Exhaustive six-coordinate classification, with no group-theoretic premise. -/
theorem coordinates_classify (P : Code → Prop) (h : ClosedCoordinates P) :
    (∀ n, P n → kernelCode n) ∨
      ∃ i : Fin 9, ∀ n, P n ↔ n ∈ candidateCodes i := by
  classical
  have p0 : P 0 := h.zero
  have neg5 : ¬ P 5 := by
    intro t5
    exact (not_mem_square h (by decide +kernel)) t5
  have neg7 : ¬ P 7 := by
    intro t7
    exact (not_mem_square h (by decide +kernel)) t7
  have neg12 : ¬ P 12 := by
    intro t12
    exact (not_mem_square h (by decide +kernel)) t12
  have neg13 : ¬ P 13 := by
    intro t13
    exact (not_mem_square h (by decide +kernel)) t13
  have neg14 : ¬ P 14 := by
    intro t14
    exact (not_mem_square h (by decide +kernel)) t14
  have neg15 : ¬ P 15 := by
    intro t15
    exact (not_mem_square h (by decide +kernel)) t15
  have neg18 : ¬ P 18 := by
    intro t18
    exact (not_mem_square h (by decide +kernel)) t18
  have neg19 : ¬ P 19 := by
    intro t19
    exact (not_mem_square h (by decide +kernel)) t19
  have neg21 : ¬ P 21 := by
    intro t21
    exact (not_mem_square h (by decide +kernel)) t21
  have neg22 : ¬ P 22 := by
    intro t22
    exact (not_mem_square h (by decide +kernel)) t22
  have neg23 : ¬ P 23 := by
    intro t23
    exact (not_mem_square h (by decide +kernel)) t23
  have neg26 : ¬ P 26 := by
    intro t26
    exact (not_mem_square h (by decide +kernel)) t26
  have neg27 : ¬ P 27 := by
    intro t27
    exact (not_mem_square h (by decide +kernel)) t27
  have neg28 : ¬ P 28 := by
    intro t28
    exact (not_mem_square h (by decide +kernel)) t28
  have neg29 : ¬ P 29 := by
    intro t29
    exact (not_mem_square h (by decide +kernel)) t29
  have neg31 : ¬ P 31 := by
    intro t31
    exact (not_mem_square h (by decide +kernel)) t31
  have neg37 : ¬ P 37 := by
    intro t37
    exact (not_mem_square h (by decide +kernel)) t37
  have neg39 : ¬ P 39 := by
    intro t39
    exact (not_mem_square h (by decide +kernel)) t39
  have neg44 : ¬ P 44 := by
    intro t44
    exact (not_mem_square h (by decide +kernel)) t44
  have neg45 : ¬ P 45 := by
    intro t45
    exact (not_mem_square h (by decide +kernel)) t45
  have neg46 : ¬ P 46 := by
    intro t46
    exact (not_mem_square h (by decide +kernel)) t46
  have neg47 : ¬ P 47 := by
    intro t47
    exact (not_mem_square h (by decide +kernel)) t47
  have neg50 : ¬ P 50 := by
    intro t50
    exact (not_mem_square h (by decide +kernel)) t50
  have neg51 : ¬ P 51 := by
    intro t51
    exact (not_mem_square h (by decide +kernel)) t51
  have neg53 : ¬ P 53 := by
    intro t53
    exact (not_mem_square h (by decide +kernel)) t53
  have neg54 : ¬ P 54 := by
    intro t54
    exact (not_mem_square h (by decide +kernel)) t54
  have neg55 : ¬ P 55 := by
    intro t55
    exact (not_mem_square h (by decide +kernel)) t55
  have neg58 : ¬ P 58 := by
    intro t58
    exact (not_mem_square h (by decide +kernel)) t58
  have neg59 : ¬ P 59 := by
    intro t59
    exact (not_mem_square h (by decide +kernel)) t59
  have neg60 : ¬ P 60 := by
    intro t60
    exact (not_mem_square h (by decide +kernel)) t60
  have neg61 : ¬ P 61 := by
    intro t61
    exact (not_mem_square h (by decide +kernel)) t61
  have neg63 : ¬ P 63 := by
    intro t63
    exact (not_mem_square h (by decide +kernel)) t63
  by_cases p8 : P 8
  ·
    have t32 : P 32 := mem_displacement h 2 p8 (by decide +kernel)
    have t40 : P 40 := mem_xor h p8 t32 (by decide +kernel)
    have neg4 : ¬ P 4 := by
      intro t4
      have t12 : P 12 := mem_xor h p8 t4 (by decide +kernel)
      exact neg12 t12
    have neg6 : ¬ P 6 := by
      intro t6
      have t14 : P 14 := mem_xor h p8 t6 (by decide +kernel)
      exact neg14 t14
    have neg20 : ¬ P 20 := by
      intro t20
      have t28 : P 28 := mem_xor h p8 t20 (by decide +kernel)
      exact neg28 t28
    have neg30 : ¬ P 30 := by
      intro t30
      have t22 : P 22 := mem_xor h p8 t30 (by decide +kernel)
      exact neg22 t22
    have neg36 : ¬ P 36 := by
      intro t36
      have t44 : P 44 := mem_xor h p8 t36 (by decide +kernel)
      exact neg44 t44
    have neg38 : ¬ P 38 := by
      intro t38
      have t46 : P 46 := mem_xor h p8 t38 (by decide +kernel)
      exact neg46 t46
    have neg52 : ¬ P 52 := by
      intro t52
      have t60 : P 60 := mem_xor h p8 t52 (by decide +kernel)
      exact neg60 t60
    have neg62 : ¬ P 62 := by
      intro t62
      have t54 : P 54 := mem_xor h p8 t62 (by decide +kernel)
      exact neg54 t54
    by_cases p1 : P 1
    ·
      have t9 : P 9 := mem_xor h p8 p1 (by decide +kernel)
      have t33 : P 33 := mem_xor h t32 p1 (by decide +kernel)
      have t41 : P 41 := mem_xor h t32 t9 (by decide +kernel)
      by_cases p2 : P 2
      ·
        have t10 : P 10 := mem_xor h p8 p2 (by decide +kernel)
        have t34 : P 34 := mem_xor h t32 p2 (by decide +kernel)
        have t42 : P 42 := mem_xor h t32 t10 (by decide +kernel)
        have t3 : P 3 := mem_xor h p1 p2 (by decide +kernel)
        have t11 : P 11 := mem_xor h p1 t10 (by decide +kernel)
        have t35 : P 35 := mem_xor h p1 t34 (by decide +kernel)
        have t43 : P 43 := mem_xor h p1 t42 (by decide +kernel)
        have neg16 : ¬ P 16 := by
          intro t16
          have t18 : P 18 := mem_xor h p2 t16 (by decide +kernel)
          exact neg18 t18
        have neg17 : ¬ P 17 := by
          intro t17
          have t19 : P 19 := mem_xor h p2 t17 (by decide +kernel)
          exact neg19 t19
        have neg24 : ¬ P 24 := by
          intro t24
          have t26 : P 26 := mem_xor h p2 t24 (by decide +kernel)
          exact neg26 t26
        have neg25 : ¬ P 25 := by
          intro t25
          have t27 : P 27 := mem_xor h p2 t25 (by decide +kernel)
          exact neg27 t27
        have neg48 : ¬ P 48 := by
          intro t48
          have t50 : P 50 := mem_xor h p2 t48 (by decide +kernel)
          exact neg50 t50
        have neg49 : ¬ P 49 := by
          intro t49
          have t51 : P 51 := mem_xor h p2 t49 (by decide +kernel)
          exact neg51 t51
        have neg56 : ¬ P 56 := by
          intro t56
          have t58 : P 58 := mem_xor h p2 t56 (by decide +kernel)
          exact neg58 t58
        have neg57 : ¬ P 57 := by
          intro t57
          have t59 : P 59 := mem_xor h p2 t57 (by decide +kernel)
          exact neg59 t59
        left
        apply forall_code
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg4 hn)
        · exact fun hn => False.elim (neg5 hn)
        · exact fun hn => False.elim (neg6 hn)
        · exact fun hn => False.elim (neg7 hn)
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg12 hn)
        · exact fun hn => False.elim (neg13 hn)
        · exact fun hn => False.elim (neg14 hn)
        · exact fun hn => False.elim (neg15 hn)
        · exact fun hn => False.elim (neg16 hn)
        · exact fun hn => False.elim (neg17 hn)
        · exact fun hn => False.elim (neg18 hn)
        · exact fun hn => False.elim (neg19 hn)
        · exact fun hn => False.elim (neg20 hn)
        · exact fun hn => False.elim (neg21 hn)
        · exact fun hn => False.elim (neg22 hn)
        · exact fun hn => False.elim (neg23 hn)
        · exact fun hn => False.elim (neg24 hn)
        · exact fun hn => False.elim (neg25 hn)
        · exact fun hn => False.elim (neg26 hn)
        · exact fun hn => False.elim (neg27 hn)
        · exact fun hn => False.elim (neg28 hn)
        · exact fun hn => False.elim (neg29 hn)
        · exact fun hn => False.elim (neg30 hn)
        · exact fun hn => False.elim (neg31 hn)
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg36 hn)
        · exact fun hn => False.elim (neg37 hn)
        · exact fun hn => False.elim (neg38 hn)
        · exact fun hn => False.elim (neg39 hn)
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg44 hn)
        · exact fun hn => False.elim (neg45 hn)
        · exact fun hn => False.elim (neg46 hn)
        · exact fun hn => False.elim (neg47 hn)
        · exact fun hn => False.elim (neg48 hn)
        · exact fun hn => False.elim (neg49 hn)
        · exact fun hn => False.elim (neg50 hn)
        · exact fun hn => False.elim (neg51 hn)
        · exact fun hn => False.elim (neg52 hn)
        · exact fun hn => False.elim (neg53 hn)
        · exact fun hn => False.elim (neg54 hn)
        · exact fun hn => False.elim (neg55 hn)
        · exact fun hn => False.elim (neg56 hn)
        · exact fun hn => False.elim (neg57 hn)
        · exact fun hn => False.elim (neg58 hn)
        · exact fun hn => False.elim (neg59 hn)
        · exact fun hn => False.elim (neg60 hn)
        · exact fun hn => False.elim (neg61 hn)
        · exact fun hn => False.elim (neg62 hn)
        · exact fun hn => False.elim (neg63 hn)
      ·
        have neg3 : ¬ P 3 := by
          intro t3
          have t2 : P 2 := mem_xor h p1 t3 (by decide +kernel)
          exact p2 t2
        have neg10 : ¬ P 10 := by
          intro t10
          have t2 : P 2 := mem_xor h p8 t10 (by decide +kernel)
          exact p2 t2
        have neg11 : ¬ P 11 := by
          intro t11
          have t3 : P 3 := mem_xor h p8 t11 (by decide +kernel)
          exact neg3 t3
        have neg34 : ¬ P 34 := by
          intro t34
          have t2 : P 2 := mem_xor h t32 t34 (by decide +kernel)
          exact p2 t2
        have neg35 : ¬ P 35 := by
          intro t35
          have t3 : P 3 := mem_xor h t32 t35 (by decide +kernel)
          exact neg3 t3
        have neg42 : ¬ P 42 := by
          intro t42
          have t34 : P 34 := mem_xor h p8 t42 (by decide +kernel)
          exact neg34 t34
        have neg43 : ¬ P 43 := by
          intro t43
          have t35 : P 35 := mem_xor h p8 t43 (by decide +kernel)
          exact neg35 t35
        by_cases p16 : P 16
        ·
          have t24 : P 24 := mem_xor h p8 p16 (by decide +kernel)
          have t48 : P 48 := mem_xor h t32 p16 (by decide +kernel)
          have t56 : P 56 := mem_xor h t32 t24 (by decide +kernel)
          have t17 : P 17 := mem_xor h p1 p16 (by decide +kernel)
          have t25 : P 25 := mem_xor h p1 t24 (by decide +kernel)
          have t49 : P 49 := mem_xor h p1 t48 (by decide +kernel)
          have t57 : P 57 := mem_xor h p1 t56 (by decide +kernel)
          refine Or.inr ⟨8, ?_⟩
          apply forall_code
          · exact iff_of_true p0 (by decide +kernel)
          · exact iff_of_true p1 (by decide +kernel)
          · exact iff_of_false p2 (by decide +kernel)
          · exact iff_of_false neg3 (by decide +kernel)
          · exact iff_of_false neg4 (by decide +kernel)
          · exact iff_of_false neg5 (by decide +kernel)
          · exact iff_of_false neg6 (by decide +kernel)
          · exact iff_of_false neg7 (by decide +kernel)
          · exact iff_of_true p8 (by decide +kernel)
          · exact iff_of_true t9 (by decide +kernel)
          · exact iff_of_false neg10 (by decide +kernel)
          · exact iff_of_false neg11 (by decide +kernel)
          · exact iff_of_false neg12 (by decide +kernel)
          · exact iff_of_false neg13 (by decide +kernel)
          · exact iff_of_false neg14 (by decide +kernel)
          · exact iff_of_false neg15 (by decide +kernel)
          · exact iff_of_true p16 (by decide +kernel)
          · exact iff_of_true t17 (by decide +kernel)
          · exact iff_of_false neg18 (by decide +kernel)
          · exact iff_of_false neg19 (by decide +kernel)
          · exact iff_of_false neg20 (by decide +kernel)
          · exact iff_of_false neg21 (by decide +kernel)
          · exact iff_of_false neg22 (by decide +kernel)
          · exact iff_of_false neg23 (by decide +kernel)
          · exact iff_of_true t24 (by decide +kernel)
          · exact iff_of_true t25 (by decide +kernel)
          · exact iff_of_false neg26 (by decide +kernel)
          · exact iff_of_false neg27 (by decide +kernel)
          · exact iff_of_false neg28 (by decide +kernel)
          · exact iff_of_false neg29 (by decide +kernel)
          · exact iff_of_false neg30 (by decide +kernel)
          · exact iff_of_false neg31 (by decide +kernel)
          · exact iff_of_true t32 (by decide +kernel)
          · exact iff_of_true t33 (by decide +kernel)
          · exact iff_of_false neg34 (by decide +kernel)
          · exact iff_of_false neg35 (by decide +kernel)
          · exact iff_of_false neg36 (by decide +kernel)
          · exact iff_of_false neg37 (by decide +kernel)
          · exact iff_of_false neg38 (by decide +kernel)
          · exact iff_of_false neg39 (by decide +kernel)
          · exact iff_of_true t40 (by decide +kernel)
          · exact iff_of_true t41 (by decide +kernel)
          · exact iff_of_false neg42 (by decide +kernel)
          · exact iff_of_false neg43 (by decide +kernel)
          · exact iff_of_false neg44 (by decide +kernel)
          · exact iff_of_false neg45 (by decide +kernel)
          · exact iff_of_false neg46 (by decide +kernel)
          · exact iff_of_false neg47 (by decide +kernel)
          · exact iff_of_true t48 (by decide +kernel)
          · exact iff_of_true t49 (by decide +kernel)
          · exact iff_of_false neg50 (by decide +kernel)
          · exact iff_of_false neg51 (by decide +kernel)
          · exact iff_of_false neg52 (by decide +kernel)
          · exact iff_of_false neg53 (by decide +kernel)
          · exact iff_of_false neg54 (by decide +kernel)
          · exact iff_of_false neg55 (by decide +kernel)
          · exact iff_of_true t56 (by decide +kernel)
          · exact iff_of_true t57 (by decide +kernel)
          · exact iff_of_false neg58 (by decide +kernel)
          · exact iff_of_false neg59 (by decide +kernel)
          · exact iff_of_false neg60 (by decide +kernel)
          · exact iff_of_false neg61 (by decide +kernel)
          · exact iff_of_false neg62 (by decide +kernel)
          · exact iff_of_false neg63 (by decide +kernel)
        ·
          have neg17 : ¬ P 17 := by
            intro t17
            have t16 : P 16 := mem_xor h p1 t17 (by decide +kernel)
            exact p16 t16
          have neg24 : ¬ P 24 := by
            intro t24
            have t16 : P 16 := mem_xor h p8 t24 (by decide +kernel)
            exact p16 t16
          have neg25 : ¬ P 25 := by
            intro t25
            have t17 : P 17 := mem_xor h p8 t25 (by decide +kernel)
            exact neg17 t17
          have neg48 : ¬ P 48 := by
            intro t48
            have t16 : P 16 := mem_xor h t32 t48 (by decide +kernel)
            exact p16 t16
          have neg49 : ¬ P 49 := by
            intro t49
            have t17 : P 17 := mem_xor h t32 t49 (by decide +kernel)
            exact neg17 t17
          have neg56 : ¬ P 56 := by
            intro t56
            have t48 : P 48 := mem_xor h p8 t56 (by decide +kernel)
            exact neg48 t48
          have neg57 : ¬ P 57 := by
            intro t57
            have t49 : P 49 := mem_xor h p8 t57 (by decide +kernel)
            exact neg49 t49
          left
          apply forall_code
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg4 hn)
          · exact fun hn => False.elim (neg5 hn)
          · exact fun hn => False.elim (neg6 hn)
          · exact fun hn => False.elim (neg7 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg12 hn)
          · exact fun hn => False.elim (neg13 hn)
          · exact fun hn => False.elim (neg14 hn)
          · exact fun hn => False.elim (neg15 hn)
          · exact fun hn => False.elim (p16 hn)
          · exact fun hn => False.elim (neg17 hn)
          · exact fun hn => False.elim (neg18 hn)
          · exact fun hn => False.elim (neg19 hn)
          · exact fun hn => False.elim (neg20 hn)
          · exact fun hn => False.elim (neg21 hn)
          · exact fun hn => False.elim (neg22 hn)
          · exact fun hn => False.elim (neg23 hn)
          · exact fun hn => False.elim (neg24 hn)
          · exact fun hn => False.elim (neg25 hn)
          · exact fun hn => False.elim (neg26 hn)
          · exact fun hn => False.elim (neg27 hn)
          · exact fun hn => False.elim (neg28 hn)
          · exact fun hn => False.elim (neg29 hn)
          · exact fun hn => False.elim (neg30 hn)
          · exact fun hn => False.elim (neg31 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg36 hn)
          · exact fun hn => False.elim (neg37 hn)
          · exact fun hn => False.elim (neg38 hn)
          · exact fun hn => False.elim (neg39 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg44 hn)
          · exact fun hn => False.elim (neg45 hn)
          · exact fun hn => False.elim (neg46 hn)
          · exact fun hn => False.elim (neg47 hn)
          · exact fun hn => False.elim (neg48 hn)
          · exact fun hn => False.elim (neg49 hn)
          · exact fun hn => False.elim (neg50 hn)
          · exact fun hn => False.elim (neg51 hn)
          · exact fun hn => False.elim (neg52 hn)
          · exact fun hn => False.elim (neg53 hn)
          · exact fun hn => False.elim (neg54 hn)
          · exact fun hn => False.elim (neg55 hn)
          · exact fun hn => False.elim (neg56 hn)
          · exact fun hn => False.elim (neg57 hn)
          · exact fun hn => False.elim (neg58 hn)
          · exact fun hn => False.elim (neg59 hn)
          · exact fun hn => False.elim (neg60 hn)
          · exact fun hn => False.elim (neg61 hn)
          · exact fun hn => False.elim (neg62 hn)
          · exact fun hn => False.elim (neg63 hn)
    ·
      have neg9 : ¬ P 9 := by
        intro t9
        have t1 : P 1 := mem_xor h p8 t9 (by decide +kernel)
        exact p1 t1
      have neg33 : ¬ P 33 := by
        intro t33
        have t1 : P 1 := mem_xor h t32 t33 (by decide +kernel)
        exact p1 t1
      have neg41 : ¬ P 41 := by
        intro t41
        have t33 : P 33 := mem_xor h p8 t41 (by decide +kernel)
        exact neg33 t33
      by_cases p2 : P 2
      ·
        have t10 : P 10 := mem_xor h p8 p2 (by decide +kernel)
        have t34 : P 34 := mem_xor h t32 p2 (by decide +kernel)
        have t42 : P 42 := mem_xor h t32 t10 (by decide +kernel)
        have neg3 : ¬ P 3 := by
          intro t3
          have t1 : P 1 := mem_xor h p2 t3 (by decide +kernel)
          exact p1 t1
        have neg11 : ¬ P 11 := by
          intro t11
          have t3 : P 3 := mem_xor h p8 t11 (by decide +kernel)
          exact neg3 t3
        have neg16 : ¬ P 16 := by
          intro t16
          have t18 : P 18 := mem_xor h p2 t16 (by decide +kernel)
          exact neg18 t18
        have neg17 : ¬ P 17 := by
          intro t17
          have t19 : P 19 := mem_xor h p2 t17 (by decide +kernel)
          exact neg19 t19
        have neg24 : ¬ P 24 := by
          intro t24
          have t26 : P 26 := mem_xor h p2 t24 (by decide +kernel)
          exact neg26 t26
        have neg25 : ¬ P 25 := by
          intro t25
          have t27 : P 27 := mem_xor h p2 t25 (by decide +kernel)
          exact neg27 t27
        have neg35 : ¬ P 35 := by
          intro t35
          have t3 : P 3 := mem_xor h t32 t35 (by decide +kernel)
          exact neg3 t3
        have neg43 : ¬ P 43 := by
          intro t43
          have t35 : P 35 := mem_xor h p8 t43 (by decide +kernel)
          exact neg35 t35
        have neg48 : ¬ P 48 := by
          intro t48
          have t50 : P 50 := mem_xor h p2 t48 (by decide +kernel)
          exact neg50 t50
        have neg49 : ¬ P 49 := by
          intro t49
          have t51 : P 51 := mem_xor h p2 t49 (by decide +kernel)
          exact neg51 t51
        have neg56 : ¬ P 56 := by
          intro t56
          have t58 : P 58 := mem_xor h p2 t56 (by decide +kernel)
          exact neg58 t58
        have neg57 : ¬ P 57 := by
          intro t57
          have t59 : P 59 := mem_xor h p2 t57 (by decide +kernel)
          exact neg59 t59
        left
        apply forall_code
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg4 hn)
        · exact fun hn => False.elim (neg5 hn)
        · exact fun hn => False.elim (neg6 hn)
        · exact fun hn => False.elim (neg7 hn)
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg12 hn)
        · exact fun hn => False.elim (neg13 hn)
        · exact fun hn => False.elim (neg14 hn)
        · exact fun hn => False.elim (neg15 hn)
        · exact fun hn => False.elim (neg16 hn)
        · exact fun hn => False.elim (neg17 hn)
        · exact fun hn => False.elim (neg18 hn)
        · exact fun hn => False.elim (neg19 hn)
        · exact fun hn => False.elim (neg20 hn)
        · exact fun hn => False.elim (neg21 hn)
        · exact fun hn => False.elim (neg22 hn)
        · exact fun hn => False.elim (neg23 hn)
        · exact fun hn => False.elim (neg24 hn)
        · exact fun hn => False.elim (neg25 hn)
        · exact fun hn => False.elim (neg26 hn)
        · exact fun hn => False.elim (neg27 hn)
        · exact fun hn => False.elim (neg28 hn)
        · exact fun hn => False.elim (neg29 hn)
        · exact fun hn => False.elim (neg30 hn)
        · exact fun hn => False.elim (neg31 hn)
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg36 hn)
        · exact fun hn => False.elim (neg37 hn)
        · exact fun hn => False.elim (neg38 hn)
        · exact fun hn => False.elim (neg39 hn)
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun _ => by decide +kernel
        · exact fun hn => False.elim (neg44 hn)
        · exact fun hn => False.elim (neg45 hn)
        · exact fun hn => False.elim (neg46 hn)
        · exact fun hn => False.elim (neg47 hn)
        · exact fun hn => False.elim (neg48 hn)
        · exact fun hn => False.elim (neg49 hn)
        · exact fun hn => False.elim (neg50 hn)
        · exact fun hn => False.elim (neg51 hn)
        · exact fun hn => False.elim (neg52 hn)
        · exact fun hn => False.elim (neg53 hn)
        · exact fun hn => False.elim (neg54 hn)
        · exact fun hn => False.elim (neg55 hn)
        · exact fun hn => False.elim (neg56 hn)
        · exact fun hn => False.elim (neg57 hn)
        · exact fun hn => False.elim (neg58 hn)
        · exact fun hn => False.elim (neg59 hn)
        · exact fun hn => False.elim (neg60 hn)
        · exact fun hn => False.elim (neg61 hn)
        · exact fun hn => False.elim (neg62 hn)
        · exact fun hn => False.elim (neg63 hn)
      ·
        have neg10 : ¬ P 10 := by
          intro t10
          have t2 : P 2 := mem_xor h p8 t10 (by decide +kernel)
          exact p2 t2
        have neg34 : ¬ P 34 := by
          intro t34
          have t2 : P 2 := mem_xor h t32 t34 (by decide +kernel)
          exact p2 t2
        have neg42 : ¬ P 42 := by
          intro t42
          have t34 : P 34 := mem_xor h p8 t42 (by decide +kernel)
          exact neg34 t34
        by_cases p3 : P 3
        ·
          have t11 : P 11 := mem_xor h p8 p3 (by decide +kernel)
          have t35 : P 35 := mem_xor h t32 p3 (by decide +kernel)
          have t43 : P 43 := mem_xor h t32 t11 (by decide +kernel)
          have neg16 : ¬ P 16 := by
            intro t16
            have t19 : P 19 := mem_xor h p3 t16 (by decide +kernel)
            exact neg19 t19
          have neg17 : ¬ P 17 := by
            intro t17
            have t18 : P 18 := mem_xor h p3 t17 (by decide +kernel)
            exact neg18 t18
          have neg24 : ¬ P 24 := by
            intro t24
            have t27 : P 27 := mem_xor h p3 t24 (by decide +kernel)
            exact neg27 t27
          have neg25 : ¬ P 25 := by
            intro t25
            have t26 : P 26 := mem_xor h p3 t25 (by decide +kernel)
            exact neg26 t26
          have neg48 : ¬ P 48 := by
            intro t48
            have t51 : P 51 := mem_xor h p3 t48 (by decide +kernel)
            exact neg51 t51
          have neg49 : ¬ P 49 := by
            intro t49
            have t50 : P 50 := mem_xor h p3 t49 (by decide +kernel)
            exact neg50 t50
          have neg56 : ¬ P 56 := by
            intro t56
            have t59 : P 59 := mem_xor h p3 t56 (by decide +kernel)
            exact neg59 t59
          have neg57 : ¬ P 57 := by
            intro t57
            have t58 : P 58 := mem_xor h p3 t57 (by decide +kernel)
            exact neg58 t58
          left
          apply forall_code
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg4 hn)
          · exact fun hn => False.elim (neg5 hn)
          · exact fun hn => False.elim (neg6 hn)
          · exact fun hn => False.elim (neg7 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg12 hn)
          · exact fun hn => False.elim (neg13 hn)
          · exact fun hn => False.elim (neg14 hn)
          · exact fun hn => False.elim (neg15 hn)
          · exact fun hn => False.elim (neg16 hn)
          · exact fun hn => False.elim (neg17 hn)
          · exact fun hn => False.elim (neg18 hn)
          · exact fun hn => False.elim (neg19 hn)
          · exact fun hn => False.elim (neg20 hn)
          · exact fun hn => False.elim (neg21 hn)
          · exact fun hn => False.elim (neg22 hn)
          · exact fun hn => False.elim (neg23 hn)
          · exact fun hn => False.elim (neg24 hn)
          · exact fun hn => False.elim (neg25 hn)
          · exact fun hn => False.elim (neg26 hn)
          · exact fun hn => False.elim (neg27 hn)
          · exact fun hn => False.elim (neg28 hn)
          · exact fun hn => False.elim (neg29 hn)
          · exact fun hn => False.elim (neg30 hn)
          · exact fun hn => False.elim (neg31 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg36 hn)
          · exact fun hn => False.elim (neg37 hn)
          · exact fun hn => False.elim (neg38 hn)
          · exact fun hn => False.elim (neg39 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg44 hn)
          · exact fun hn => False.elim (neg45 hn)
          · exact fun hn => False.elim (neg46 hn)
          · exact fun hn => False.elim (neg47 hn)
          · exact fun hn => False.elim (neg48 hn)
          · exact fun hn => False.elim (neg49 hn)
          · exact fun hn => False.elim (neg50 hn)
          · exact fun hn => False.elim (neg51 hn)
          · exact fun hn => False.elim (neg52 hn)
          · exact fun hn => False.elim (neg53 hn)
          · exact fun hn => False.elim (neg54 hn)
          · exact fun hn => False.elim (neg55 hn)
          · exact fun hn => False.elim (neg56 hn)
          · exact fun hn => False.elim (neg57 hn)
          · exact fun hn => False.elim (neg58 hn)
          · exact fun hn => False.elim (neg59 hn)
          · exact fun hn => False.elim (neg60 hn)
          · exact fun hn => False.elim (neg61 hn)
          · exact fun hn => False.elim (neg62 hn)
          · exact fun hn => False.elim (neg63 hn)
        ·
          have neg11 : ¬ P 11 := by
            intro t11
            have t3 : P 3 := mem_xor h p8 t11 (by decide +kernel)
            exact p3 t3
          have neg35 : ¬ P 35 := by
            intro t35
            have t3 : P 3 := mem_xor h t32 t35 (by decide +kernel)
            exact p3 t3
          have neg43 : ¬ P 43 := by
            intro t43
            have t35 : P 35 := mem_xor h p8 t43 (by decide +kernel)
            exact neg35 t35
          by_cases p16 : P 16
          ·
            have t24 : P 24 := mem_xor h p8 p16 (by decide +kernel)
            have t48 : P 48 := mem_xor h t32 p16 (by decide +kernel)
            have t56 : P 56 := mem_xor h t32 t24 (by decide +kernel)
            have neg17 : ¬ P 17 := by
              intro t17
              have t1 : P 1 := mem_xor h p16 t17 (by decide +kernel)
              exact p1 t1
            have neg25 : ¬ P 25 := by
              intro t25
              have t17 : P 17 := mem_xor h p8 t25 (by decide +kernel)
              exact neg17 t17
            have neg49 : ¬ P 49 := by
              intro t49
              have t17 : P 17 := mem_xor h t32 t49 (by decide +kernel)
              exact neg17 t17
            have neg57 : ¬ P 57 := by
              intro t57
              have t49 : P 49 := mem_xor h p8 t57 (by decide +kernel)
              exact neg49 t49
            refine Or.inr ⟨7, ?_⟩
            apply forall_code
            · exact iff_of_true p0 (by decide +kernel)
            · exact iff_of_false p1 (by decide +kernel)
            · exact iff_of_false p2 (by decide +kernel)
            · exact iff_of_false p3 (by decide +kernel)
            · exact iff_of_false neg4 (by decide +kernel)
            · exact iff_of_false neg5 (by decide +kernel)
            · exact iff_of_false neg6 (by decide +kernel)
            · exact iff_of_false neg7 (by decide +kernel)
            · exact iff_of_true p8 (by decide +kernel)
            · exact iff_of_false neg9 (by decide +kernel)
            · exact iff_of_false neg10 (by decide +kernel)
            · exact iff_of_false neg11 (by decide +kernel)
            · exact iff_of_false neg12 (by decide +kernel)
            · exact iff_of_false neg13 (by decide +kernel)
            · exact iff_of_false neg14 (by decide +kernel)
            · exact iff_of_false neg15 (by decide +kernel)
            · exact iff_of_true p16 (by decide +kernel)
            · exact iff_of_false neg17 (by decide +kernel)
            · exact iff_of_false neg18 (by decide +kernel)
            · exact iff_of_false neg19 (by decide +kernel)
            · exact iff_of_false neg20 (by decide +kernel)
            · exact iff_of_false neg21 (by decide +kernel)
            · exact iff_of_false neg22 (by decide +kernel)
            · exact iff_of_false neg23 (by decide +kernel)
            · exact iff_of_true t24 (by decide +kernel)
            · exact iff_of_false neg25 (by decide +kernel)
            · exact iff_of_false neg26 (by decide +kernel)
            · exact iff_of_false neg27 (by decide +kernel)
            · exact iff_of_false neg28 (by decide +kernel)
            · exact iff_of_false neg29 (by decide +kernel)
            · exact iff_of_false neg30 (by decide +kernel)
            · exact iff_of_false neg31 (by decide +kernel)
            · exact iff_of_true t32 (by decide +kernel)
            · exact iff_of_false neg33 (by decide +kernel)
            · exact iff_of_false neg34 (by decide +kernel)
            · exact iff_of_false neg35 (by decide +kernel)
            · exact iff_of_false neg36 (by decide +kernel)
            · exact iff_of_false neg37 (by decide +kernel)
            · exact iff_of_false neg38 (by decide +kernel)
            · exact iff_of_false neg39 (by decide +kernel)
            · exact iff_of_true t40 (by decide +kernel)
            · exact iff_of_false neg41 (by decide +kernel)
            · exact iff_of_false neg42 (by decide +kernel)
            · exact iff_of_false neg43 (by decide +kernel)
            · exact iff_of_false neg44 (by decide +kernel)
            · exact iff_of_false neg45 (by decide +kernel)
            · exact iff_of_false neg46 (by decide +kernel)
            · exact iff_of_false neg47 (by decide +kernel)
            · exact iff_of_true t48 (by decide +kernel)
            · exact iff_of_false neg49 (by decide +kernel)
            · exact iff_of_false neg50 (by decide +kernel)
            · exact iff_of_false neg51 (by decide +kernel)
            · exact iff_of_false neg52 (by decide +kernel)
            · exact iff_of_false neg53 (by decide +kernel)
            · exact iff_of_false neg54 (by decide +kernel)
            · exact iff_of_false neg55 (by decide +kernel)
            · exact iff_of_true t56 (by decide +kernel)
            · exact iff_of_false neg57 (by decide +kernel)
            · exact iff_of_false neg58 (by decide +kernel)
            · exact iff_of_false neg59 (by decide +kernel)
            · exact iff_of_false neg60 (by decide +kernel)
            · exact iff_of_false neg61 (by decide +kernel)
            · exact iff_of_false neg62 (by decide +kernel)
            · exact iff_of_false neg63 (by decide +kernel)
          ·
            have neg24 : ¬ P 24 := by
              intro t24
              have t16 : P 16 := mem_xor h p8 t24 (by decide +kernel)
              exact p16 t16
            have neg48 : ¬ P 48 := by
              intro t48
              have t16 : P 16 := mem_xor h t32 t48 (by decide +kernel)
              exact p16 t16
            have neg56 : ¬ P 56 := by
              intro t56
              have t48 : P 48 := mem_xor h p8 t56 (by decide +kernel)
              exact neg48 t48
            by_cases p17 : P 17
            ·
              have t25 : P 25 := mem_xor h p8 p17 (by decide +kernel)
              have t49 : P 49 := mem_xor h t32 p17 (by decide +kernel)
              have t57 : P 57 := mem_xor h t32 t25 (by decide +kernel)
              refine Or.inr ⟨3, ?_⟩
              apply forall_code
              · exact iff_of_true p0 (by decide +kernel)
              · exact iff_of_false p1 (by decide +kernel)
              · exact iff_of_false p2 (by decide +kernel)
              · exact iff_of_false p3 (by decide +kernel)
              · exact iff_of_false neg4 (by decide +kernel)
              · exact iff_of_false neg5 (by decide +kernel)
              · exact iff_of_false neg6 (by decide +kernel)
              · exact iff_of_false neg7 (by decide +kernel)
              · exact iff_of_true p8 (by decide +kernel)
              · exact iff_of_false neg9 (by decide +kernel)
              · exact iff_of_false neg10 (by decide +kernel)
              · exact iff_of_false neg11 (by decide +kernel)
              · exact iff_of_false neg12 (by decide +kernel)
              · exact iff_of_false neg13 (by decide +kernel)
              · exact iff_of_false neg14 (by decide +kernel)
              · exact iff_of_false neg15 (by decide +kernel)
              · exact iff_of_false p16 (by decide +kernel)
              · exact iff_of_true p17 (by decide +kernel)
              · exact iff_of_false neg18 (by decide +kernel)
              · exact iff_of_false neg19 (by decide +kernel)
              · exact iff_of_false neg20 (by decide +kernel)
              · exact iff_of_false neg21 (by decide +kernel)
              · exact iff_of_false neg22 (by decide +kernel)
              · exact iff_of_false neg23 (by decide +kernel)
              · exact iff_of_false neg24 (by decide +kernel)
              · exact iff_of_true t25 (by decide +kernel)
              · exact iff_of_false neg26 (by decide +kernel)
              · exact iff_of_false neg27 (by decide +kernel)
              · exact iff_of_false neg28 (by decide +kernel)
              · exact iff_of_false neg29 (by decide +kernel)
              · exact iff_of_false neg30 (by decide +kernel)
              · exact iff_of_false neg31 (by decide +kernel)
              · exact iff_of_true t32 (by decide +kernel)
              · exact iff_of_false neg33 (by decide +kernel)
              · exact iff_of_false neg34 (by decide +kernel)
              · exact iff_of_false neg35 (by decide +kernel)
              · exact iff_of_false neg36 (by decide +kernel)
              · exact iff_of_false neg37 (by decide +kernel)
              · exact iff_of_false neg38 (by decide +kernel)
              · exact iff_of_false neg39 (by decide +kernel)
              · exact iff_of_true t40 (by decide +kernel)
              · exact iff_of_false neg41 (by decide +kernel)
              · exact iff_of_false neg42 (by decide +kernel)
              · exact iff_of_false neg43 (by decide +kernel)
              · exact iff_of_false neg44 (by decide +kernel)
              · exact iff_of_false neg45 (by decide +kernel)
              · exact iff_of_false neg46 (by decide +kernel)
              · exact iff_of_false neg47 (by decide +kernel)
              · exact iff_of_false neg48 (by decide +kernel)
              · exact iff_of_true t49 (by decide +kernel)
              · exact iff_of_false neg50 (by decide +kernel)
              · exact iff_of_false neg51 (by decide +kernel)
              · exact iff_of_false neg52 (by decide +kernel)
              · exact iff_of_false neg53 (by decide +kernel)
              · exact iff_of_false neg54 (by decide +kernel)
              · exact iff_of_false neg55 (by decide +kernel)
              · exact iff_of_false neg56 (by decide +kernel)
              · exact iff_of_true t57 (by decide +kernel)
              · exact iff_of_false neg58 (by decide +kernel)
              · exact iff_of_false neg59 (by decide +kernel)
              · exact iff_of_false neg60 (by decide +kernel)
              · exact iff_of_false neg61 (by decide +kernel)
              · exact iff_of_false neg62 (by decide +kernel)
              · exact iff_of_false neg63 (by decide +kernel)
            ·
              have neg25 : ¬ P 25 := by
                intro t25
                have t17 : P 17 := mem_xor h p8 t25 (by decide +kernel)
                exact p17 t17
              have neg49 : ¬ P 49 := by
                intro t49
                have t17 : P 17 := mem_xor h t32 t49 (by decide +kernel)
                exact p17 t17
              have neg57 : ¬ P 57 := by
                intro t57
                have t49 : P 49 := mem_xor h p8 t57 (by decide +kernel)
                exact neg49 t49
              left
              apply forall_code
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun hn => False.elim (neg4 hn)
              · exact fun hn => False.elim (neg5 hn)
              · exact fun hn => False.elim (neg6 hn)
              · exact fun hn => False.elim (neg7 hn)
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun hn => False.elim (neg12 hn)
              · exact fun hn => False.elim (neg13 hn)
              · exact fun hn => False.elim (neg14 hn)
              · exact fun hn => False.elim (neg15 hn)
              · exact fun hn => False.elim (p16 hn)
              · exact fun hn => False.elim (p17 hn)
              · exact fun hn => False.elim (neg18 hn)
              · exact fun hn => False.elim (neg19 hn)
              · exact fun hn => False.elim (neg20 hn)
              · exact fun hn => False.elim (neg21 hn)
              · exact fun hn => False.elim (neg22 hn)
              · exact fun hn => False.elim (neg23 hn)
              · exact fun hn => False.elim (neg24 hn)
              · exact fun hn => False.elim (neg25 hn)
              · exact fun hn => False.elim (neg26 hn)
              · exact fun hn => False.elim (neg27 hn)
              · exact fun hn => False.elim (neg28 hn)
              · exact fun hn => False.elim (neg29 hn)
              · exact fun hn => False.elim (neg30 hn)
              · exact fun hn => False.elim (neg31 hn)
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun hn => False.elim (neg36 hn)
              · exact fun hn => False.elim (neg37 hn)
              · exact fun hn => False.elim (neg38 hn)
              · exact fun hn => False.elim (neg39 hn)
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun _ => by decide +kernel
              · exact fun hn => False.elim (neg44 hn)
              · exact fun hn => False.elim (neg45 hn)
              · exact fun hn => False.elim (neg46 hn)
              · exact fun hn => False.elim (neg47 hn)
              · exact fun hn => False.elim (neg48 hn)
              · exact fun hn => False.elim (neg49 hn)
              · exact fun hn => False.elim (neg50 hn)
              · exact fun hn => False.elim (neg51 hn)
              · exact fun hn => False.elim (neg52 hn)
              · exact fun hn => False.elim (neg53 hn)
              · exact fun hn => False.elim (neg54 hn)
              · exact fun hn => False.elim (neg55 hn)
              · exact fun hn => False.elim (neg56 hn)
              · exact fun hn => False.elim (neg57 hn)
              · exact fun hn => False.elim (neg58 hn)
              · exact fun hn => False.elim (neg59 hn)
              · exact fun hn => False.elim (neg60 hn)
              · exact fun hn => False.elim (neg61 hn)
              · exact fun hn => False.elim (neg62 hn)
              · exact fun hn => False.elim (neg63 hn)
  ·
    have neg1 : ¬ P 1 := by
      intro t1
      have t8 : P 8 := mem_displacement h 4 t1 (by decide +kernel)
      exact p8 t8
    have neg2 : ¬ P 2 := by
      intro t2
      have t40 : P 40 := mem_displacement h 1 t2 (by decide +kernel)
      have t32 : P 32 := mem_displacement h 3 t2 (by decide +kernel)
      have t8 : P 8 := mem_xor h t40 t32 (by decide +kernel)
      exact p8 t8
    have neg3 : ¬ P 3 := by
      intro t3
      have t8 : P 8 := mem_displacement h 4 t3 (by decide +kernel)
      exact p8 t8
    have neg9 : ¬ P 9 := by
      intro t9
      have t8 : P 8 := mem_displacement h 4 t9 (by decide +kernel)
      exact p8 t8
    have neg10 : ¬ P 10 := by
      intro t10
      have t40 : P 40 := mem_displacement h 1 t10 (by decide +kernel)
      have t32 : P 32 := mem_displacement h 2 t10 (by decide +kernel)
      have t8 : P 8 := mem_xor h t40 t32 (by decide +kernel)
      exact p8 t8
    have neg11 : ¬ P 11 := by
      intro t11
      have t8 : P 8 := mem_displacement h 4 t11 (by decide +kernel)
      exact p8 t8
    have neg17 : ¬ P 17 := by
      intro t17
      have t8 : P 8 := mem_displacement h 4 t17 (by decide +kernel)
      exact p8 t8
    have neg25 : ¬ P 25 := by
      intro t25
      have t8 : P 8 := mem_displacement h 4 t25 (by decide +kernel)
      exact p8 t8
    have neg33 : ¬ P 33 := by
      intro t33
      have t8 : P 8 := mem_displacement h 4 t33 (by decide +kernel)
      exact p8 t8
    have neg34 : ¬ P 34 := by
      intro t34
      have t40 : P 40 := mem_displacement h 1 t34 (by decide +kernel)
      have t10 : P 10 := mem_xor h t34 t40 (by decide +kernel)
      exact neg10 t10
    have neg35 : ¬ P 35 := by
      intro t35
      have t8 : P 8 := mem_displacement h 4 t35 (by decide +kernel)
      exact p8 t8
    have neg40 : ¬ P 40 := by
      intro t40
      have t32 : P 32 := mem_displacement h 2 t40 (by decide +kernel)
      have t8 : P 8 := mem_xor h t40 t32 (by decide +kernel)
      exact p8 t8
    have neg41 : ¬ P 41 := by
      intro t41
      have t40 : P 40 := mem_displacement h 0 t41 (by decide +kernel)
      exact neg40 t40
    have neg42 : ¬ P 42 := by
      intro t42
      have t40 : P 40 := mem_displacement h 1 t42 (by decide +kernel)
      exact neg40 t40
    have neg43 : ¬ P 43 := by
      intro t43
      have t40 : P 40 := mem_displacement h 0 t43 (by decide +kernel)
      exact neg40 t40
    have neg49 : ¬ P 49 := by
      intro t49
      have t40 : P 40 := mem_displacement h 0 t49 (by decide +kernel)
      exact neg40 t40
    have neg57 : ¬ P 57 := by
      intro t57
      have t40 : P 40 := mem_displacement h 0 t57 (by decide +kernel)
      exact neg40 t40
    by_cases p16 : P 16
    ·
      have neg6 : ¬ P 6 := by
        intro t6
        have t22 : P 22 := mem_xor h p16 t6 (by decide +kernel)
        exact neg22 t22
      have neg24 : ¬ P 24 := by
        intro t24
        have t8 : P 8 := mem_xor h p16 t24 (by decide +kernel)
        exact p8 t8
      have neg30 : ¬ P 30 := by
        intro t30
        have t14 : P 14 := mem_xor h p16 t30 (by decide +kernel)
        exact neg14 t14
      have neg38 : ¬ P 38 := by
        intro t38
        have t54 : P 54 := mem_xor h p16 t38 (by decide +kernel)
        exact neg54 t54
      have neg56 : ¬ P 56 := by
        intro t56
        have t40 : P 40 := mem_xor h p16 t56 (by decide +kernel)
        exact neg40 t40
      have neg62 : ¬ P 62 := by
        intro t62
        have t46 : P 46 := mem_xor h p16 t62 (by decide +kernel)
        exact neg46 t46
      by_cases p4 : P 4
      ·
        have t20 : P 20 := mem_xor h p16 p4 (by decide +kernel)
        have t32 : P 32 := mem_displacement h 0 p4 (by decide +kernel)
        have t36 : P 36 := mem_xor h p4 t32 (by decide +kernel)
        have t52 : P 52 := mem_xor h t20 t32 (by decide +kernel)
        have t48 : P 48 := mem_xor h t20 t36 (by decide +kernel)
        refine Or.inr ⟨6, ?_⟩
        apply forall_code
        · exact iff_of_true p0 (by decide +kernel)
        · exact iff_of_false neg1 (by decide +kernel)
        · exact iff_of_false neg2 (by decide +kernel)
        · exact iff_of_false neg3 (by decide +kernel)
        · exact iff_of_true p4 (by decide +kernel)
        · exact iff_of_false neg5 (by decide +kernel)
        · exact iff_of_false neg6 (by decide +kernel)
        · exact iff_of_false neg7 (by decide +kernel)
        · exact iff_of_false p8 (by decide +kernel)
        · exact iff_of_false neg9 (by decide +kernel)
        · exact iff_of_false neg10 (by decide +kernel)
        · exact iff_of_false neg11 (by decide +kernel)
        · exact iff_of_false neg12 (by decide +kernel)
        · exact iff_of_false neg13 (by decide +kernel)
        · exact iff_of_false neg14 (by decide +kernel)
        · exact iff_of_false neg15 (by decide +kernel)
        · exact iff_of_true p16 (by decide +kernel)
        · exact iff_of_false neg17 (by decide +kernel)
        · exact iff_of_false neg18 (by decide +kernel)
        · exact iff_of_false neg19 (by decide +kernel)
        · exact iff_of_true t20 (by decide +kernel)
        · exact iff_of_false neg21 (by decide +kernel)
        · exact iff_of_false neg22 (by decide +kernel)
        · exact iff_of_false neg23 (by decide +kernel)
        · exact iff_of_false neg24 (by decide +kernel)
        · exact iff_of_false neg25 (by decide +kernel)
        · exact iff_of_false neg26 (by decide +kernel)
        · exact iff_of_false neg27 (by decide +kernel)
        · exact iff_of_false neg28 (by decide +kernel)
        · exact iff_of_false neg29 (by decide +kernel)
        · exact iff_of_false neg30 (by decide +kernel)
        · exact iff_of_false neg31 (by decide +kernel)
        · exact iff_of_true t32 (by decide +kernel)
        · exact iff_of_false neg33 (by decide +kernel)
        · exact iff_of_false neg34 (by decide +kernel)
        · exact iff_of_false neg35 (by decide +kernel)
        · exact iff_of_true t36 (by decide +kernel)
        · exact iff_of_false neg37 (by decide +kernel)
        · exact iff_of_false neg38 (by decide +kernel)
        · exact iff_of_false neg39 (by decide +kernel)
        · exact iff_of_false neg40 (by decide +kernel)
        · exact iff_of_false neg41 (by decide +kernel)
        · exact iff_of_false neg42 (by decide +kernel)
        · exact iff_of_false neg43 (by decide +kernel)
        · exact iff_of_false neg44 (by decide +kernel)
        · exact iff_of_false neg45 (by decide +kernel)
        · exact iff_of_false neg46 (by decide +kernel)
        · exact iff_of_false neg47 (by decide +kernel)
        · exact iff_of_true t48 (by decide +kernel)
        · exact iff_of_false neg49 (by decide +kernel)
        · exact iff_of_false neg50 (by decide +kernel)
        · exact iff_of_false neg51 (by decide +kernel)
        · exact iff_of_true t52 (by decide +kernel)
        · exact iff_of_false neg53 (by decide +kernel)
        · exact iff_of_false neg54 (by decide +kernel)
        · exact iff_of_false neg55 (by decide +kernel)
        · exact iff_of_false neg56 (by decide +kernel)
        · exact iff_of_false neg57 (by decide +kernel)
        · exact iff_of_false neg58 (by decide +kernel)
        · exact iff_of_false neg59 (by decide +kernel)
        · exact iff_of_false neg60 (by decide +kernel)
        · exact iff_of_false neg61 (by decide +kernel)
        · exact iff_of_false neg62 (by decide +kernel)
        · exact iff_of_false neg63 (by decide +kernel)
      ·
        have neg20 : ¬ P 20 := by
          intro t20
          have t4 : P 4 := mem_xor h p16 t20 (by decide +kernel)
          exact p4 t4
        have neg36 : ¬ P 36 := by
          intro t36
          have t32 : P 32 := mem_displacement h 0 t36 (by decide +kernel)
          have t4 : P 4 := mem_xor h t36 t32 (by decide +kernel)
          exact p4 t4
        have neg52 : ¬ P 52 := by
          intro t52
          have t36 : P 36 := mem_xor h p16 t52 (by decide +kernel)
          exact neg36 t36
        by_cases p32 : P 32
        ·
          have t48 : P 48 := mem_xor h p16 p32 (by decide +kernel)
          refine Or.inr ⟨5, ?_⟩
          apply forall_code
          · exact iff_of_true p0 (by decide +kernel)
          · exact iff_of_false neg1 (by decide +kernel)
          · exact iff_of_false neg2 (by decide +kernel)
          · exact iff_of_false neg3 (by decide +kernel)
          · exact iff_of_false p4 (by decide +kernel)
          · exact iff_of_false neg5 (by decide +kernel)
          · exact iff_of_false neg6 (by decide +kernel)
          · exact iff_of_false neg7 (by decide +kernel)
          · exact iff_of_false p8 (by decide +kernel)
          · exact iff_of_false neg9 (by decide +kernel)
          · exact iff_of_false neg10 (by decide +kernel)
          · exact iff_of_false neg11 (by decide +kernel)
          · exact iff_of_false neg12 (by decide +kernel)
          · exact iff_of_false neg13 (by decide +kernel)
          · exact iff_of_false neg14 (by decide +kernel)
          · exact iff_of_false neg15 (by decide +kernel)
          · exact iff_of_true p16 (by decide +kernel)
          · exact iff_of_false neg17 (by decide +kernel)
          · exact iff_of_false neg18 (by decide +kernel)
          · exact iff_of_false neg19 (by decide +kernel)
          · exact iff_of_false neg20 (by decide +kernel)
          · exact iff_of_false neg21 (by decide +kernel)
          · exact iff_of_false neg22 (by decide +kernel)
          · exact iff_of_false neg23 (by decide +kernel)
          · exact iff_of_false neg24 (by decide +kernel)
          · exact iff_of_false neg25 (by decide +kernel)
          · exact iff_of_false neg26 (by decide +kernel)
          · exact iff_of_false neg27 (by decide +kernel)
          · exact iff_of_false neg28 (by decide +kernel)
          · exact iff_of_false neg29 (by decide +kernel)
          · exact iff_of_false neg30 (by decide +kernel)
          · exact iff_of_false neg31 (by decide +kernel)
          · exact iff_of_true p32 (by decide +kernel)
          · exact iff_of_false neg33 (by decide +kernel)
          · exact iff_of_false neg34 (by decide +kernel)
          · exact iff_of_false neg35 (by decide +kernel)
          · exact iff_of_false neg36 (by decide +kernel)
          · exact iff_of_false neg37 (by decide +kernel)
          · exact iff_of_false neg38 (by decide +kernel)
          · exact iff_of_false neg39 (by decide +kernel)
          · exact iff_of_false neg40 (by decide +kernel)
          · exact iff_of_false neg41 (by decide +kernel)
          · exact iff_of_false neg42 (by decide +kernel)
          · exact iff_of_false neg43 (by decide +kernel)
          · exact iff_of_false neg44 (by decide +kernel)
          · exact iff_of_false neg45 (by decide +kernel)
          · exact iff_of_false neg46 (by decide +kernel)
          · exact iff_of_false neg47 (by decide +kernel)
          · exact iff_of_true t48 (by decide +kernel)
          · exact iff_of_false neg49 (by decide +kernel)
          · exact iff_of_false neg50 (by decide +kernel)
          · exact iff_of_false neg51 (by decide +kernel)
          · exact iff_of_false neg52 (by decide +kernel)
          · exact iff_of_false neg53 (by decide +kernel)
          · exact iff_of_false neg54 (by decide +kernel)
          · exact iff_of_false neg55 (by decide +kernel)
          · exact iff_of_false neg56 (by decide +kernel)
          · exact iff_of_false neg57 (by decide +kernel)
          · exact iff_of_false neg58 (by decide +kernel)
          · exact iff_of_false neg59 (by decide +kernel)
          · exact iff_of_false neg60 (by decide +kernel)
          · exact iff_of_false neg61 (by decide +kernel)
          · exact iff_of_false neg62 (by decide +kernel)
          · exact iff_of_false neg63 (by decide +kernel)
        ·
          have neg48 : ¬ P 48 := by
            intro t48
            have t32 : P 32 := mem_xor h p16 t48 (by decide +kernel)
            exact p32 t32
          refine Or.inr ⟨1, ?_⟩
          apply forall_code
          · exact iff_of_true p0 (by decide +kernel)
          · exact iff_of_false neg1 (by decide +kernel)
          · exact iff_of_false neg2 (by decide +kernel)
          · exact iff_of_false neg3 (by decide +kernel)
          · exact iff_of_false p4 (by decide +kernel)
          · exact iff_of_false neg5 (by decide +kernel)
          · exact iff_of_false neg6 (by decide +kernel)
          · exact iff_of_false neg7 (by decide +kernel)
          · exact iff_of_false p8 (by decide +kernel)
          · exact iff_of_false neg9 (by decide +kernel)
          · exact iff_of_false neg10 (by decide +kernel)
          · exact iff_of_false neg11 (by decide +kernel)
          · exact iff_of_false neg12 (by decide +kernel)
          · exact iff_of_false neg13 (by decide +kernel)
          · exact iff_of_false neg14 (by decide +kernel)
          · exact iff_of_false neg15 (by decide +kernel)
          · exact iff_of_true p16 (by decide +kernel)
          · exact iff_of_false neg17 (by decide +kernel)
          · exact iff_of_false neg18 (by decide +kernel)
          · exact iff_of_false neg19 (by decide +kernel)
          · exact iff_of_false neg20 (by decide +kernel)
          · exact iff_of_false neg21 (by decide +kernel)
          · exact iff_of_false neg22 (by decide +kernel)
          · exact iff_of_false neg23 (by decide +kernel)
          · exact iff_of_false neg24 (by decide +kernel)
          · exact iff_of_false neg25 (by decide +kernel)
          · exact iff_of_false neg26 (by decide +kernel)
          · exact iff_of_false neg27 (by decide +kernel)
          · exact iff_of_false neg28 (by decide +kernel)
          · exact iff_of_false neg29 (by decide +kernel)
          · exact iff_of_false neg30 (by decide +kernel)
          · exact iff_of_false neg31 (by decide +kernel)
          · exact iff_of_false p32 (by decide +kernel)
          · exact iff_of_false neg33 (by decide +kernel)
          · exact iff_of_false neg34 (by decide +kernel)
          · exact iff_of_false neg35 (by decide +kernel)
          · exact iff_of_false neg36 (by decide +kernel)
          · exact iff_of_false neg37 (by decide +kernel)
          · exact iff_of_false neg38 (by decide +kernel)
          · exact iff_of_false neg39 (by decide +kernel)
          · exact iff_of_false neg40 (by decide +kernel)
          · exact iff_of_false neg41 (by decide +kernel)
          · exact iff_of_false neg42 (by decide +kernel)
          · exact iff_of_false neg43 (by decide +kernel)
          · exact iff_of_false neg44 (by decide +kernel)
          · exact iff_of_false neg45 (by decide +kernel)
          · exact iff_of_false neg46 (by decide +kernel)
          · exact iff_of_false neg47 (by decide +kernel)
          · exact iff_of_false neg48 (by decide +kernel)
          · exact iff_of_false neg49 (by decide +kernel)
          · exact iff_of_false neg50 (by decide +kernel)
          · exact iff_of_false neg51 (by decide +kernel)
          · exact iff_of_false neg52 (by decide +kernel)
          · exact iff_of_false neg53 (by decide +kernel)
          · exact iff_of_false neg54 (by decide +kernel)
          · exact iff_of_false neg55 (by decide +kernel)
          · exact iff_of_false neg56 (by decide +kernel)
          · exact iff_of_false neg57 (by decide +kernel)
          · exact iff_of_false neg58 (by decide +kernel)
          · exact iff_of_false neg59 (by decide +kernel)
          · exact iff_of_false neg60 (by decide +kernel)
          · exact iff_of_false neg61 (by decide +kernel)
          · exact iff_of_false neg62 (by decide +kernel)
          · exact iff_of_false neg63 (by decide +kernel)
    ·
      have neg4 : ¬ P 4 := by
        intro t4
        have t16 : P 16 := mem_displacement h 1 t4 (by decide +kernel)
        exact p16 t16
      have neg20 : ¬ P 20 := by
        intro t20
        have t16 : P 16 := mem_displacement h 1 t20 (by decide +kernel)
        exact p16 t16
      have neg36 : ¬ P 36 := by
        intro t36
        have t16 : P 16 := mem_displacement h 1 t36 (by decide +kernel)
        exact p16 t16
      have neg52 : ¬ P 52 := by
        intro t52
        have t16 : P 16 := mem_displacement h 1 t52 (by decide +kernel)
        exact p16 t16
      by_cases p24 : P 24
      ·
        have t32 : P 32 := mem_displacement h 2 p24 (by decide +kernel)
        have t56 : P 56 := mem_xor h p24 t32 (by decide +kernel)
        have neg48 : ¬ P 48 := by
          intro t48
          have t40 : P 40 := mem_xor h p24 t48 (by decide +kernel)
          exact neg40 t40
        by_cases p6 : P 6
        ·
          have t30 : P 30 := mem_xor h p24 p6 (by decide +kernel)
          have t38 : P 38 := mem_xor h t32 p6 (by decide +kernel)
          have t62 : P 62 := mem_xor h t32 t30 (by decide +kernel)
          refine Or.inr ⟨4, ?_⟩
          apply forall_code
          · exact iff_of_true p0 (by decide +kernel)
          · exact iff_of_false neg1 (by decide +kernel)
          · exact iff_of_false neg2 (by decide +kernel)
          · exact iff_of_false neg3 (by decide +kernel)
          · exact iff_of_false neg4 (by decide +kernel)
          · exact iff_of_false neg5 (by decide +kernel)
          · exact iff_of_true p6 (by decide +kernel)
          · exact iff_of_false neg7 (by decide +kernel)
          · exact iff_of_false p8 (by decide +kernel)
          · exact iff_of_false neg9 (by decide +kernel)
          · exact iff_of_false neg10 (by decide +kernel)
          · exact iff_of_false neg11 (by decide +kernel)
          · exact iff_of_false neg12 (by decide +kernel)
          · exact iff_of_false neg13 (by decide +kernel)
          · exact iff_of_false neg14 (by decide +kernel)
          · exact iff_of_false neg15 (by decide +kernel)
          · exact iff_of_false p16 (by decide +kernel)
          · exact iff_of_false neg17 (by decide +kernel)
          · exact iff_of_false neg18 (by decide +kernel)
          · exact iff_of_false neg19 (by decide +kernel)
          · exact iff_of_false neg20 (by decide +kernel)
          · exact iff_of_false neg21 (by decide +kernel)
          · exact iff_of_false neg22 (by decide +kernel)
          · exact iff_of_false neg23 (by decide +kernel)
          · exact iff_of_true p24 (by decide +kernel)
          · exact iff_of_false neg25 (by decide +kernel)
          · exact iff_of_false neg26 (by decide +kernel)
          · exact iff_of_false neg27 (by decide +kernel)
          · exact iff_of_false neg28 (by decide +kernel)
          · exact iff_of_false neg29 (by decide +kernel)
          · exact iff_of_true t30 (by decide +kernel)
          · exact iff_of_false neg31 (by decide +kernel)
          · exact iff_of_true t32 (by decide +kernel)
          · exact iff_of_false neg33 (by decide +kernel)
          · exact iff_of_false neg34 (by decide +kernel)
          · exact iff_of_false neg35 (by decide +kernel)
          · exact iff_of_false neg36 (by decide +kernel)
          · exact iff_of_false neg37 (by decide +kernel)
          · exact iff_of_true t38 (by decide +kernel)
          · exact iff_of_false neg39 (by decide +kernel)
          · exact iff_of_false neg40 (by decide +kernel)
          · exact iff_of_false neg41 (by decide +kernel)
          · exact iff_of_false neg42 (by decide +kernel)
          · exact iff_of_false neg43 (by decide +kernel)
          · exact iff_of_false neg44 (by decide +kernel)
          · exact iff_of_false neg45 (by decide +kernel)
          · exact iff_of_false neg46 (by decide +kernel)
          · exact iff_of_false neg47 (by decide +kernel)
          · exact iff_of_false neg48 (by decide +kernel)
          · exact iff_of_false neg49 (by decide +kernel)
          · exact iff_of_false neg50 (by decide +kernel)
          · exact iff_of_false neg51 (by decide +kernel)
          · exact iff_of_false neg52 (by decide +kernel)
          · exact iff_of_false neg53 (by decide +kernel)
          · exact iff_of_false neg54 (by decide +kernel)
          · exact iff_of_false neg55 (by decide +kernel)
          · exact iff_of_true t56 (by decide +kernel)
          · exact iff_of_false neg57 (by decide +kernel)
          · exact iff_of_false neg58 (by decide +kernel)
          · exact iff_of_false neg59 (by decide +kernel)
          · exact iff_of_false neg60 (by decide +kernel)
          · exact iff_of_false neg61 (by decide +kernel)
          · exact iff_of_true t62 (by decide +kernel)
          · exact iff_of_false neg63 (by decide +kernel)
        ·
          have neg30 : ¬ P 30 := by
            intro t30
            have t6 : P 6 := mem_xor h p24 t30 (by decide +kernel)
            exact p6 t6
          have neg38 : ¬ P 38 := by
            intro t38
            have t6 : P 6 := mem_xor h t32 t38 (by decide +kernel)
            exact p6 t6
          have neg62 : ¬ P 62 := by
            intro t62
            have t38 : P 38 := mem_xor h p24 t62 (by decide +kernel)
            exact neg38 t38
          refine Or.inr ⟨2, ?_⟩
          apply forall_code
          · exact iff_of_true p0 (by decide +kernel)
          · exact iff_of_false neg1 (by decide +kernel)
          · exact iff_of_false neg2 (by decide +kernel)
          · exact iff_of_false neg3 (by decide +kernel)
          · exact iff_of_false neg4 (by decide +kernel)
          · exact iff_of_false neg5 (by decide +kernel)
          · exact iff_of_false p6 (by decide +kernel)
          · exact iff_of_false neg7 (by decide +kernel)
          · exact iff_of_false p8 (by decide +kernel)
          · exact iff_of_false neg9 (by decide +kernel)
          · exact iff_of_false neg10 (by decide +kernel)
          · exact iff_of_false neg11 (by decide +kernel)
          · exact iff_of_false neg12 (by decide +kernel)
          · exact iff_of_false neg13 (by decide +kernel)
          · exact iff_of_false neg14 (by decide +kernel)
          · exact iff_of_false neg15 (by decide +kernel)
          · exact iff_of_false p16 (by decide +kernel)
          · exact iff_of_false neg17 (by decide +kernel)
          · exact iff_of_false neg18 (by decide +kernel)
          · exact iff_of_false neg19 (by decide +kernel)
          · exact iff_of_false neg20 (by decide +kernel)
          · exact iff_of_false neg21 (by decide +kernel)
          · exact iff_of_false neg22 (by decide +kernel)
          · exact iff_of_false neg23 (by decide +kernel)
          · exact iff_of_true p24 (by decide +kernel)
          · exact iff_of_false neg25 (by decide +kernel)
          · exact iff_of_false neg26 (by decide +kernel)
          · exact iff_of_false neg27 (by decide +kernel)
          · exact iff_of_false neg28 (by decide +kernel)
          · exact iff_of_false neg29 (by decide +kernel)
          · exact iff_of_false neg30 (by decide +kernel)
          · exact iff_of_false neg31 (by decide +kernel)
          · exact iff_of_true t32 (by decide +kernel)
          · exact iff_of_false neg33 (by decide +kernel)
          · exact iff_of_false neg34 (by decide +kernel)
          · exact iff_of_false neg35 (by decide +kernel)
          · exact iff_of_false neg36 (by decide +kernel)
          · exact iff_of_false neg37 (by decide +kernel)
          · exact iff_of_false neg38 (by decide +kernel)
          · exact iff_of_false neg39 (by decide +kernel)
          · exact iff_of_false neg40 (by decide +kernel)
          · exact iff_of_false neg41 (by decide +kernel)
          · exact iff_of_false neg42 (by decide +kernel)
          · exact iff_of_false neg43 (by decide +kernel)
          · exact iff_of_false neg44 (by decide +kernel)
          · exact iff_of_false neg45 (by decide +kernel)
          · exact iff_of_false neg46 (by decide +kernel)
          · exact iff_of_false neg47 (by decide +kernel)
          · exact iff_of_false neg48 (by decide +kernel)
          · exact iff_of_false neg49 (by decide +kernel)
          · exact iff_of_false neg50 (by decide +kernel)
          · exact iff_of_false neg51 (by decide +kernel)
          · exact iff_of_false neg52 (by decide +kernel)
          · exact iff_of_false neg53 (by decide +kernel)
          · exact iff_of_false neg54 (by decide +kernel)
          · exact iff_of_false neg55 (by decide +kernel)
          · exact iff_of_true t56 (by decide +kernel)
          · exact iff_of_false neg57 (by decide +kernel)
          · exact iff_of_false neg58 (by decide +kernel)
          · exact iff_of_false neg59 (by decide +kernel)
          · exact iff_of_false neg60 (by decide +kernel)
          · exact iff_of_false neg61 (by decide +kernel)
          · exact iff_of_false neg62 (by decide +kernel)
          · exact iff_of_false neg63 (by decide +kernel)
      ·
        have neg6 : ¬ P 6 := by
          intro t6
          have t32 : P 32 := mem_displacement h 0 t6 (by decide +kernel)
          have t56 : P 56 := mem_displacement h 1 t6 (by decide +kernel)
          have t24 : P 24 := mem_xor h t32 t56 (by decide +kernel)
          exact p24 t24
        have neg30 : ¬ P 30 := by
          intro t30
          have t32 : P 32 := mem_displacement h 0 t30 (by decide +kernel)
          have t56 : P 56 := mem_displacement h 1 t30 (by decide +kernel)
          have t24 : P 24 := mem_xor h t32 t56 (by decide +kernel)
          exact p24 t24
        have neg38 : ¬ P 38 := by
          intro t38
          have t32 : P 32 := mem_displacement h 0 t38 (by decide +kernel)
          have t6 : P 6 := mem_xor h t38 t32 (by decide +kernel)
          exact neg6 t6
        have neg56 : ¬ P 56 := by
          intro t56
          have t32 : P 32 := mem_displacement h 2 t56 (by decide +kernel)
          have t24 : P 24 := mem_xor h t56 t32 (by decide +kernel)
          exact p24 t24
        have neg62 : ¬ P 62 := by
          intro t62
          have t56 : P 56 := mem_displacement h 1 t62 (by decide +kernel)
          exact neg56 t56
        by_cases p32 : P 32
        ·
          have neg48 : ¬ P 48 := by
            intro t48
            have t16 : P 16 := mem_xor h p32 t48 (by decide +kernel)
            exact p16 t16
          left
          apply forall_code
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg4 hn)
          · exact fun hn => False.elim (neg5 hn)
          · exact fun hn => False.elim (neg6 hn)
          · exact fun hn => False.elim (neg7 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg12 hn)
          · exact fun hn => False.elim (neg13 hn)
          · exact fun hn => False.elim (neg14 hn)
          · exact fun hn => False.elim (neg15 hn)
          · exact fun hn => False.elim (p16 hn)
          · exact fun hn => False.elim (neg17 hn)
          · exact fun hn => False.elim (neg18 hn)
          · exact fun hn => False.elim (neg19 hn)
          · exact fun hn => False.elim (neg20 hn)
          · exact fun hn => False.elim (neg21 hn)
          · exact fun hn => False.elim (neg22 hn)
          · exact fun hn => False.elim (neg23 hn)
          · exact fun hn => False.elim (p24 hn)
          · exact fun hn => False.elim (neg25 hn)
          · exact fun hn => False.elim (neg26 hn)
          · exact fun hn => False.elim (neg27 hn)
          · exact fun hn => False.elim (neg28 hn)
          · exact fun hn => False.elim (neg29 hn)
          · exact fun hn => False.elim (neg30 hn)
          · exact fun hn => False.elim (neg31 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg36 hn)
          · exact fun hn => False.elim (neg37 hn)
          · exact fun hn => False.elim (neg38 hn)
          · exact fun hn => False.elim (neg39 hn)
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun _ => by decide +kernel
          · exact fun hn => False.elim (neg44 hn)
          · exact fun hn => False.elim (neg45 hn)
          · exact fun hn => False.elim (neg46 hn)
          · exact fun hn => False.elim (neg47 hn)
          · exact fun hn => False.elim (neg48 hn)
          · exact fun hn => False.elim (neg49 hn)
          · exact fun hn => False.elim (neg50 hn)
          · exact fun hn => False.elim (neg51 hn)
          · exact fun hn => False.elim (neg52 hn)
          · exact fun hn => False.elim (neg53 hn)
          · exact fun hn => False.elim (neg54 hn)
          · exact fun hn => False.elim (neg55 hn)
          · exact fun hn => False.elim (neg56 hn)
          · exact fun hn => False.elim (neg57 hn)
          · exact fun hn => False.elim (neg58 hn)
          · exact fun hn => False.elim (neg59 hn)
          · exact fun hn => False.elim (neg60 hn)
          · exact fun hn => False.elim (neg61 hn)
          · exact fun hn => False.elim (neg62 hn)
          · exact fun hn => False.elim (neg63 hn)
        ·
          by_cases p48 : P 48
          ·
            refine Or.inr ⟨0, ?_⟩
            apply forall_code
            · exact iff_of_true p0 (by decide +kernel)
            · exact iff_of_false neg1 (by decide +kernel)
            · exact iff_of_false neg2 (by decide +kernel)
            · exact iff_of_false neg3 (by decide +kernel)
            · exact iff_of_false neg4 (by decide +kernel)
            · exact iff_of_false neg5 (by decide +kernel)
            · exact iff_of_false neg6 (by decide +kernel)
            · exact iff_of_false neg7 (by decide +kernel)
            · exact iff_of_false p8 (by decide +kernel)
            · exact iff_of_false neg9 (by decide +kernel)
            · exact iff_of_false neg10 (by decide +kernel)
            · exact iff_of_false neg11 (by decide +kernel)
            · exact iff_of_false neg12 (by decide +kernel)
            · exact iff_of_false neg13 (by decide +kernel)
            · exact iff_of_false neg14 (by decide +kernel)
            · exact iff_of_false neg15 (by decide +kernel)
            · exact iff_of_false p16 (by decide +kernel)
            · exact iff_of_false neg17 (by decide +kernel)
            · exact iff_of_false neg18 (by decide +kernel)
            · exact iff_of_false neg19 (by decide +kernel)
            · exact iff_of_false neg20 (by decide +kernel)
            · exact iff_of_false neg21 (by decide +kernel)
            · exact iff_of_false neg22 (by decide +kernel)
            · exact iff_of_false neg23 (by decide +kernel)
            · exact iff_of_false p24 (by decide +kernel)
            · exact iff_of_false neg25 (by decide +kernel)
            · exact iff_of_false neg26 (by decide +kernel)
            · exact iff_of_false neg27 (by decide +kernel)
            · exact iff_of_false neg28 (by decide +kernel)
            · exact iff_of_false neg29 (by decide +kernel)
            · exact iff_of_false neg30 (by decide +kernel)
            · exact iff_of_false neg31 (by decide +kernel)
            · exact iff_of_false p32 (by decide +kernel)
            · exact iff_of_false neg33 (by decide +kernel)
            · exact iff_of_false neg34 (by decide +kernel)
            · exact iff_of_false neg35 (by decide +kernel)
            · exact iff_of_false neg36 (by decide +kernel)
            · exact iff_of_false neg37 (by decide +kernel)
            · exact iff_of_false neg38 (by decide +kernel)
            · exact iff_of_false neg39 (by decide +kernel)
            · exact iff_of_false neg40 (by decide +kernel)
            · exact iff_of_false neg41 (by decide +kernel)
            · exact iff_of_false neg42 (by decide +kernel)
            · exact iff_of_false neg43 (by decide +kernel)
            · exact iff_of_false neg44 (by decide +kernel)
            · exact iff_of_false neg45 (by decide +kernel)
            · exact iff_of_false neg46 (by decide +kernel)
            · exact iff_of_false neg47 (by decide +kernel)
            · exact iff_of_true p48 (by decide +kernel)
            · exact iff_of_false neg49 (by decide +kernel)
            · exact iff_of_false neg50 (by decide +kernel)
            · exact iff_of_false neg51 (by decide +kernel)
            · exact iff_of_false neg52 (by decide +kernel)
            · exact iff_of_false neg53 (by decide +kernel)
            · exact iff_of_false neg54 (by decide +kernel)
            · exact iff_of_false neg55 (by decide +kernel)
            · exact iff_of_false neg56 (by decide +kernel)
            · exact iff_of_false neg57 (by decide +kernel)
            · exact iff_of_false neg58 (by decide +kernel)
            · exact iff_of_false neg59 (by decide +kernel)
            · exact iff_of_false neg60 (by decide +kernel)
            · exact iff_of_false neg61 (by decide +kernel)
            · exact iff_of_false neg62 (by decide +kernel)
            · exact iff_of_false neg63 (by decide +kernel)
          ·
            left
            apply forall_code
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun hn => False.elim (neg4 hn)
            · exact fun hn => False.elim (neg5 hn)
            · exact fun hn => False.elim (neg6 hn)
            · exact fun hn => False.elim (neg7 hn)
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun hn => False.elim (neg12 hn)
            · exact fun hn => False.elim (neg13 hn)
            · exact fun hn => False.elim (neg14 hn)
            · exact fun hn => False.elim (neg15 hn)
            · exact fun hn => False.elim (p16 hn)
            · exact fun hn => False.elim (neg17 hn)
            · exact fun hn => False.elim (neg18 hn)
            · exact fun hn => False.elim (neg19 hn)
            · exact fun hn => False.elim (neg20 hn)
            · exact fun hn => False.elim (neg21 hn)
            · exact fun hn => False.elim (neg22 hn)
            · exact fun hn => False.elim (neg23 hn)
            · exact fun hn => False.elim (p24 hn)
            · exact fun hn => False.elim (neg25 hn)
            · exact fun hn => False.elim (neg26 hn)
            · exact fun hn => False.elim (neg27 hn)
            · exact fun hn => False.elim (neg28 hn)
            · exact fun hn => False.elim (neg29 hn)
            · exact fun hn => False.elim (neg30 hn)
            · exact fun hn => False.elim (neg31 hn)
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun hn => False.elim (neg36 hn)
            · exact fun hn => False.elim (neg37 hn)
            · exact fun hn => False.elim (neg38 hn)
            · exact fun hn => False.elim (neg39 hn)
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun _ => by decide +kernel
            · exact fun hn => False.elim (neg44 hn)
            · exact fun hn => False.elim (neg45 hn)
            · exact fun hn => False.elim (neg46 hn)
            · exact fun hn => False.elim (neg47 hn)
            · exact fun hn => False.elim (p48 hn)
            · exact fun hn => False.elim (neg49 hn)
            · exact fun hn => False.elim (neg50 hn)
            · exact fun hn => False.elim (neg51 hn)
            · exact fun hn => False.elim (neg52 hn)
            · exact fun hn => False.elim (neg53 hn)
            · exact fun hn => False.elim (neg54 hn)
            · exact fun hn => False.elim (neg55 hn)
            · exact fun hn => False.elim (neg56 hn)
            · exact fun hn => False.elim (neg57 hn)
            · exact fun hn => False.elim (neg58 hn)
            · exact fun hn => False.elim (neg59 hn)
            · exact fun hn => False.elim (neg60 hn)
            · exact fun hn => False.elim (neg61 hn)
            · exact fun hn => False.elim (neg62 hn)
            · exact fun hn => False.elim (neg63 hn)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue
