module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Group

/-!
# The ten positive roots in the Ree two centralizer core

The index `i : Fin 10` denotes Shinoda's root `i + 3`. The square and
commutator tables below are the specialization at `q = 2` of (2.3),
pp. 81–82 of K. Shinoda, *A characterization of odd order extensions of the
Ree groups ²F₄(q)*, J. Fac. Sci. Univ. Tokyo IA **22** (1975), 79–102.
They involve only roots 3 through 12; in particular the disputed printed
relation for roots 2 and 3 is not a defining relation here.

We use the right commutator `a⁻¹ * b⁻¹ * a * b`, as in the source
calculation. Right conjugation by `a` is Lean's `MulAut.conj a⁻¹`,
not `MulAut.conj a`. The tables specify relations in an arbitrary group;
no finiteness or consistency claim is built into this interface.
-/

@[expose] public section
namespace ReeTwo

abbrev CoreRoot := Fin 10

/-- Evaluation in increasing written order, with no commutativity convention. -/
def rootWord {G : Type*} [Group G] (x : CoreRoot → G) (w : List CoreRoot) : G :=
  (w.map x).prod

@[simp] theorem rootWord_nil {G : Type*} [Group G] (x : CoreRoot → G) :
    rootWord x [] = 1 := rfl

@[simp] theorem rootWord_cons {G : Type*} [Group G] (x : CoreRoot → G)
    (i : CoreRoot) (w : List CoreRoot) : rootWord x (i :: w) = x i * rootWord x w := rfl

@[simp] theorem rootWord_append {G : Type*} [Group G] (x : CoreRoot → G)
    (u v : List CoreRoot) : rootWord x (u ++ v) = rootWord x u * rootWord x v := by
  simp [rootWord]

/-- The source's right commutator, distinct from Mathlib's left commutator. -/
def rightComm {G : Type*} [Group G] (a b : G) : G := a⁻¹ * b⁻¹ * a * b

/-- The square of root 4, 5, or 6 is root 8, 12, or 11 respectively. -/
def coreSquare (i : CoreRoot) : List CoreRoot :=
  match i.val with
  | 1 => [5]
  | 2 => [9]
  | 3 => [8]
  | _ => []

/-- The nontrivial entries of the core commutator table, with zero based indices. -/
def coreCommutator (i j : CoreRoot) : List CoreRoot :=
  match i.val, j.val with
  | 0, 2 => [5]
  | 0, 3 => [5, 6, 9]
  | 0, 4 => [6, 7]
  | 0, 8 => [9]
  | 1, 2 => [6]
  | 1, 4 => [7, 8, 9]
  | 1, 7 => [9]
  | 2, 3 => [7]
  | 2, 4 => [8]
  | 3, 6 => [9]
  | 4, 5 => [9]
  | _, _ => []

/-- All squares and all pairwise commutators, including the unlisted trivial ones. -/
structure CoreRelations {G : Type*} [Group G] (x : CoreRoot → G) : Prop where
  square (i : CoreRoot) : x i * x i = rootWord x (coreSquare i)
  commutator (i j : CoreRoot) (hij : i < j) :
    rightComm (x i) (x j) = rootWord x (coreCommutator i j)

/-- The correction in the action of root 1 on a core generator:
`x₁⁻¹ * xᵢ * x₁ = xᵢ * (rootWord x (actionCorrection i))⁻¹`. -/
def actionCorrection (i : CoreRoot) : List CoreRoot :=
  match i.val with
  | 0 => [1, 2, 4, 8, 9]
  | 1 => [2, 3, 4, 6, 7, 8, 9]
  | 3 => [4]
  | 5 => [6, 8, 9]
  | 6 => [7, 8, 9]
  | 7 => [8]
  | _ => []

/-- Root 1's specified right-conjugation action, expressed using commutators. -/
def RootOneRelations {G : Type*} [Group G] (a : G) (x : CoreRoot → G) : Prop :=
  ∀ i, rightComm a (x i) = rootWord x (actionCorrection i)

/-- The Weyl involution on the core, from Shinoda's table on p. 81. -/
def weylRoot (i : CoreRoot) : CoreRoot :=
  match i.val with
  | 0 => 4
  | 1 => 3
  | 2 => 2
  | 3 => 1
  | 4 => 0
  | 5 => 8
  | 6 => 7
  | 7 => 6
  | 8 => 5
  | _ => 9

theorem rightConj_of_rightComm {G : Type*} [Group G] {a b c : G}
    (h : rightComm a b = c) : MulAut.conj a⁻¹ b = b * c⁻¹ := by
  rw [← h]
  simp [rightComm, mul_assoc]

theorem rightComm_square {G : Type*} [Group G] (a b : G) :
    rightComm (a ^ 2) b = MulAut.conj a⁻¹ (rightComm a b) * rightComm a b := by
  simp [rightComm, pow_two, mul_assoc]

end ReeTwo
