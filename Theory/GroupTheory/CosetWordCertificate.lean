module

public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Kernel checked coset-word certificates

A fact `(i,w,j)` asserts `repr i * eval w = h * repr j` for some `h ∈ H`.
The six rules are reflexivity, defining edges, subgroup loops at the identity,
relator loops, reversal, and composition with free reduction. Their soundness
uses actual equalities in an arbitrary group, without finiteness assumptions.

The intended producer is the six-rule coset trace for Parrott's presentation
(see `refs/original/n-group-global/parrott-tits-presentation.md`). The producer
is untrusted. `check` checks one instruction against explicit fact data; the
soundness theorem supports independently checked chunks or named proof DAG
nodes. In particular it never evaluates a recursively reconstructed history.

Signed words use Mathlib's `(generator, positive)` convention. `decodeLetter`
translates the producer's numeric encoding `2*k`, `2*k+1`. Free reduction is
justified by a structural induction cancelling adjacent inverse letters. Acyclic
defining trees realize the representatives, and signed output facts give a
`GeneratorCosetCover`.
-/

@[expose] public section

namespace Subgroup.CosetWordCertificate

abbrev Letter (α : Type*) := α × Bool
abbrev Word (α : Type*) := List (Letter α)

/-- Numeric even letters are positive; odd letters are negative. -/
def decodeLetter (a : Nat) : Letter Nat := (a / 2, a % 2 == 0)

@[simp] theorem decodeLetter_even (k : Nat) : decodeLetter (2 * k) = (k, true) := by
  simp [decodeLetter]

@[simp] theorem decodeLetter_odd (k : Nat) : decodeLetter (2 * k + 1) = (k, false) := by
  simp [decodeLetter, Nat.add_div]

/-- Evaluation of a signed word in an arbitrary group. -/
def eval {G α : Type*} [Group G] (g : α → G) (w : Word α) : G :=
  FreeGroup.lift g (FreeGroup.mk w)

@[simp] theorem eval_nil {G α : Type*} [Group G] (g : α → G) : eval g [] = 1 := by
  simp [eval]

theorem eval_append {G α : Type*} [Group G] (g : α → G) (u v : Word α) :
    eval g (u ++ v) = eval g u * eval g v := by
  exact (map_mul (FreeGroup.lift g) (FreeGroup.mk u) (FreeGroup.mk v))

@[simp] theorem eval_letter {G α : Type*} [Group G] (g : α → G) (a : Letter α) :
    eval g [a] = if a.2 then g a.1 else (g a.1)⁻¹ := by
  simp [eval, FreeGroup.lift_mk]

theorem eval_invRev {G α : Type*} [Group G] (g : α → G) (w : Word α) :
    eval g (FreeGroup.invRev w) = (eval g w)⁻¹ := by
  exact map_inv (FreeGroup.lift g) (FreeGroup.mk w)

/-- Cancel adjacent inverse letters, processing the tail first. Each letter is
visited once, and each recursive step performs one head comparison. -/
def reduce {α : Type*} [DecidableEq α] : Word α → Word α
  | [] => []
  | a :: w =>
      match reduce w with
      | [] => [a]
      | b :: v => if b = (a.1, !a.2) then v else a :: b :: v

theorem eval_cons {G α : Type*} [Group G] (g : α → G)
    (a : Letter α) (w : Word α) :
    eval g (a :: w) = (if a.2 then g a.1 else (g a.1)⁻¹) * eval g w := by
  rw [← eval_letter g a]
  exact eval_append g [a] w

theorem eval_reduce {G α : Type*} [Group G] [DecidableEq α]
    (g : α → G) (w : Word α) : eval g (reduce w) = eval g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [reduce, eval_cons, ← ih]
    cases h : reduce w with
    | nil => simp
    | cons b v =>
      simp only
      split
      · rename_i hb
        subst b
        cases a with
        | mk x sign => cases sign <;> simp [eval_cons]
      · simp only [eval_cons]

theorem eval_append_reduce {G α : Type*} [Group G] [DecidableEq α]
    (g : α → G) (u v : Word α) :
    eval g (reduce (u ++ v)) = eval g u * eval g v := by
  rw [eval_reduce, eval_append]

/-- Explicit data at a DAG node. Named constants for these data prevent history
recomputation in generated certificates. -/
structure FactData (α : Type*) where
  left : Nat
  word : Word α
  right : Nat
  deriving DecidableEq, Repr

/-- The mathematical meaning of one fact. -/
def Holds {G α : Type*} [Group G] (H : Subgroup G) (g : α → G)
    (repr : Nat → G) (f : FactData α) : Prop :=
  ∃ h : H, repr f.left * eval g f.word = h.val * repr f.right

variable {G α : Type*} [Group G] {H : Subgroup G} {g : α → G}
  {ρ : Nat → G}

theorem holds_refl (i : Nat) : Holds H g ρ ⟨i, [], i⟩ :=
  ⟨1, by simp⟩

theorem holds_defining (i j : Nat) (a : Letter α)
    (he : ρ i * eval g [a] = ρ j) : Holds H g ρ ⟨i, [a], j⟩ :=
  ⟨1, by simpa using he⟩

theorem holds_subgroup (hroot : ρ 0 = 1) (a : Letter α)
    (ha : eval g [a] ∈ H) : Holds H g ρ ⟨0, [a], 0⟩ :=
  ⟨⟨eval g [a], ha⟩, by simp [hroot]⟩

theorem holds_relator (i : Nat) (w : Word α) (hw : eval g w = 1) :
    Holds H g ρ ⟨i, w, i⟩ :=
  ⟨1, by simp [hw]⟩

theorem holds_reverse {f : FactData α} (hf : Holds H g ρ f) :
    Holds H g ρ ⟨f.right, FreeGroup.invRev f.word, f.left⟩ := by
  obtain ⟨h, hh⟩ := hf
  refine ⟨h⁻¹, ?_⟩
  change ρ f.right * eval g (FreeGroup.invRev f.word) = (h.val)⁻¹ * ρ f.left
  rw [eval_invRev]
  have he := congrArg (fun x => h.val⁻¹ * x * (eval g f.word)⁻¹) hh
  simpa [mul_assoc] using he.symm

theorem holds_compose [DecidableEq α] {f₁ f₂ : FactData α}
    (hm : f₁.right = f₂.left) (h₁ : Holds H g ρ f₁)
    (h₂ : Holds H g ρ f₂) :
    Holds H g ρ ⟨f₁.left, reduce (f₁.word ++ f₂.word), f₂.right⟩ := by
  obtain ⟨h₁', e₁⟩ := h₁
  obtain ⟨h₂', e₂⟩ := h₂
  refine ⟨h₁' * h₂', ?_⟩
  change ρ f₁.left * eval g (reduce (f₁.word ++ f₂.word)) =
    (h₁'.val * h₂'.val) * ρ f₂.right
  rw [eval_append_reduce, ← mul_assoc, e₁, mul_assoc, hm, e₂, ← mul_assoc]

/-- An acyclic defining tree. Node zero is the root; every other parent is
strictly smaller. Finite input tables can be extended with parent zero. -/
structure Definitions (α : Type*) where
  parent : Nat → Nat
  letter : Nat → Letter α
  parent_lt : ∀ n, parent (n + 1) < n + 1

/-- Realize the tree directly in the ambient group. No word normalization or
choice of coset representatives is required. -/
def Definitions.repr (D : Definitions α) (g : α → G) (n : Nat) : G :=
  match n with
  | 0 => 1
  | k + 1 => D.repr g (D.parent (k + 1)) * eval g [D.letter (k + 1)]
termination_by n
decreasing_by exact D.parent_lt _

@[simp] theorem Definitions.repr_zero (D : Definitions α) (g : α → G) :
    D.repr g 0 = 1 := by rw [Definitions.repr]

theorem Definitions.repr_edge (D : Definitions α) (g : α → G) (j : Nat) (hj : j ≠ 0) :
    D.repr g (D.parent j) * eval g [D.letter j] = D.repr g j := by
  cases j with
  | zero => exact (hj rfl).elim
  | succ k => rw [Definitions.repr]

/-- Syntactic context. The bounds on relator indices and allowed subgroup
letters are represented by finite lists/arrays by the client if desired. -/
structure Context (α : Type*) where
  parent : Nat → Nat
  letter : Nat → Letter α
  relator : Nat → Word α
  allowed : Letter α → Bool

/-- Only actual group equalities and subgroup membership validate a context.
Defining edges at zero are excluded by the checker. -/
structure Valid (C : Context α) (H : Subgroup G) (g : α → G) (ρ : Nat → G) : Prop where
  root : ρ 0 = 1
  edge : ∀ j, j ≠ 0 → ρ (C.parent j) * eval g [C.letter j] = ρ j
  subgroup : ∀ a, C.allowed a = true → eval g [a] ∈ H
  relator : ∀ r, eval g (C.relator r) = 1

/-- Realized acyclic definitions discharge all defining-edge obligations. -/
theorem Definitions.valid (D : Definitions α) (rels : Nat → Word α)
    (allowed : Letter α → Bool) (hs : ∀ a, allowed a = true → eval g [a] ∈ H)
    (hr : ∀ r, eval g (rels r) = 1) :
    Valid ⟨D.parent, D.letter, rels, allowed⟩ H g (D.repr g) :=
  ⟨D.repr_zero g, D.repr_edge g, hs, hr⟩

/-- The six trace instructions. `defining j` takes a node index, independently
of the instruction's own index. -/
inductive Instruction (α : Type*) where
  | refl (i : Nat)
  | defining (j : Nat)
  | subgroup (a : Letter α)
  | relator (i r : Nat)
  | reverse (p : Nat)
  | compose (p q : Nat)
  deriving Repr

/-- Which earlier facts an instruction uses. -/
def Instruction.Uses (op : Instruction α) (p : Nat) : Prop :=
  match op with
  | .reverse q => p = q
  | .compose q r => p = q ∨ p = r
  | _ => False

/-- Local Boolean checker. References must be smaller than `n`; no recursive
lookup of instructions or growing prefix list occurs here. `facts` must store
explicit results, rather than recursively recomputing them from instructions. -/
def check [DecidableEq α] (C : Context α) (facts : Nat → FactData α)
    (n : Nat) (op : Instruction α) (out : FactData α) : Bool :=
  match op with
  | .refl i => decide (out = ⟨i, [], i⟩)
  | .defining j => decide (j ≠ 0 ∧ out = ⟨C.parent j, [C.letter j], j⟩)
  | .subgroup a => C.allowed a && decide (out = ⟨0, [a], 0⟩)
  | .relator i r => decide (out = ⟨i, C.relator r, i⟩)
  | .reverse p => decide (p < n ∧
      out = ⟨(facts p).right, FreeGroup.invRev (facts p).word, (facts p).left⟩)
  | .compose p q => decide (p < n ∧ q < n ∧ (facts p).right = (facts q).left ∧
      out = ⟨(facts p).left, reduce ((facts p).word ++ (facts q).word),
        (facts q).right⟩)

/-- Soundness of one DAG node. The hypotheses mention only its actual
predecessors, so consumers may supply named previous theorems. -/
theorem check_sound [DecidableEq α] {C : Context α} (hC : Valid C H g ρ)
    (facts : Nat → FactData α) (n : Nat) (op : Instruction α) (out : FactData α)
    (hc : check C facts n op out = true)
    (prev : ∀ p, p < n → op.Uses p → Holds H g ρ (facts p)) :
    Holds H g ρ out := by
  cases op with
  | refl i =>
      simp only [check, decide_eq_true_eq] at hc
      subst out
      exact holds_refl i
  | defining j =>
      simp only [check, decide_eq_true_eq] at hc
      rcases hc with ⟨hj, rfl⟩
      exact holds_defining _ _ _ (hC.edge j hj)
  | subgroup a =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨ha, rfl⟩
      exact holds_subgroup hC.root a (hC.subgroup a ha)
  | relator i r =>
      simp only [check, decide_eq_true_eq] at hc
      subst out
      exact holds_relator i _ (hC.relator r)
  | reverse p =>
      simp only [check, decide_eq_true_eq] at hc
      rcases hc with ⟨hp, rfl⟩
      exact holds_reverse (prev p hp rfl)
  | compose p q =>
      simp only [check, decide_eq_true_eq] at hc
      rcases hc with ⟨hp, hq, hm, rfl⟩
      exact holds_compose hm (prev p hp (Or.inl rfl)) (prev q hq (Or.inr rfl))

/-- Soundness for a finite trace, from local checks. The theorem needs no
monolithic computation: its check hypotheses may come from separate chunks. -/
theorem sound [DecidableEq α] {C : Context α} (hC : Valid C H g ρ)
    (facts : Nat → FactData α) (ops : Nat → Instruction α) (N : Nat)
    (checked : ∀ n, n < N → check C facts n (ops n) (facts n) = true) :
    ∀ n, n < N → Holds H g ρ (facts n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      exact check_sound hC facts n (ops n) (facts n) (checked n hn)
        (fun p hp _ => ih p hp (hp.trans hn))

/-- A checked interval extends an already proved prefix. This provides chunk
boundaries without rerunning or copying the preceding trace. -/
theorem sound_chunk [DecidableEq α] {C : Context α} (hC : Valid C H g ρ)
    (facts : Nat → FactData α) (ops : Nat → Instruction α) (lo hi : Nat)
    (prior : ∀ n, n < lo → Holds H g ρ (facts n))
    (checked : ∀ n, lo ≤ n → n < hi → check C facts n (ops n) (facts n) = true) :
    ∀ n, n < hi → Holds H g ρ (facts n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hl : n < lo
      · exact prior n hl
      · exact check_sound hC facts n (ops n) (facts n)
          (checked n (Nat.le_of_not_gt hl) hn)
          (fun p hp _ => ih p hp (hp.trans hn))

/-- Check a bounded block against explicit shared fact data. Prove concrete
instances with kernel `decide` or `rfl`, never `native_decide`. Use a bounded
chunk size and a balanced lookup or named constants for the shared table. -/
def checkChunk [DecidableEq α] (C : Context α) (facts : Nat → FactData α)
    (ops : Nat → Instruction α) (start count : Nat) : Bool :=
  (List.range count).all (fun k => check C facts (start + k) (ops (start + k))
    (facts (start + k)))

/-- The executable block check supplies the hypotheses of `sound_chunk`. -/
theorem checkChunk_sound [DecidableEq α] {C : Context α} (hC : Valid C H g ρ)
    (facts : Nat → FactData α) (ops : Nat → Instruction α) (start count : Nat)
    (prior : ∀ n, n < start → Holds H g ρ (facts n))
    (checked : checkChunk C facts ops start count = true) :
    ∀ n, n < start + count → Holds H g ρ (facts n) := by
  apply sound_chunk hC facts ops start (start + count) prior
  intro n hlo hhi
  have he : start + (n - start) = n := Nat.add_sub_of_le hlo
  have hmem : n - start ∈ List.range count := by
    simp only [List.mem_range]
    omega
  have hc := List.all_eq_true.mp checked (n - start) hmem
  simpa only [he] using hc

/-- Signed singleton facts supply both fields of a generator coset cover.
The survivor indexing need not be injective, and no finiteness is assumed. -/
def generatorCosetCover {ι : Type*} (index : ι → Nat) (initial : ι)
    (hzero : ρ (index initial) = 1)
    (dest : ι → Letter α → ι)
    (transitions : ∀ i a, Holds H g ρ ⟨index i, [a], index (dest i a)⟩) :
    Subgroup.GeneratorCosetCover H g ι where
  repr i := ρ (index i)
  initial := initial
  initial_eq := hzero
  step i a := by
    obtain ⟨h, hh⟩ := transitions i (a, true)
    exact ⟨h, dest i (a, true), by simpa using hh⟩
  inv_step i a := by
    obtain ⟨h, hh⟩ := transitions i (a, false)
    exact ⟨h, dest i (a, false), by simpa using hh⟩

/-- Extract a cover from selected nodes of a sound trace. -/
def coverOfFacts {ι : Type*} (facts : Nat → FactData α)
    (index : ι → Nat) (initial : ι) (hzero : ρ (index initial) = 1)
    (dest : ι → Letter α → ι) (output : ι → Letter α → Nat)
    (shape : ∀ i a, facts (output i a) = ⟨index i, [a], index (dest i a)⟩)
    (valid : ∀ i a, Holds H g ρ (facts (output i a))) :
    Subgroup.GeneratorCosetCover H g ι :=
  generatorCosetCover index initial hzero dest (fun i a => shape i a ▸ valid i a)

end Subgroup.CosetWordCertificate
