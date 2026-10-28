module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.Inputs
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Embedding-sensitive obligations for the proper-pair sieve

The group to be calculated is the pointwise fixer of the actual embedded L
in Aut(I). For perfect L, `Transport` identifies this with the centralizer
of its inner action. The five Lie rows and the L₃(2) row in J₂ must have
fixer order less than four. In the remaining rows we request an upper bound
of four and exponent dividing two. The faithful order-four action will give
the reverse inequality; no elementary-abelian hypothesis on E is needed.

These are outstanding model obligations, not assertions of the tables. In
particular the HS bound does not assert order four for every A₈ embedding.
The full nine-way `ProperModels` list remains the input to the sieve.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.7(3), printed pp.1172–1173, and 16.3.5, pp.1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory ClassificationModels
open CounterexampleGeometry.CoveredPersistence
variable {G : Type*} [Group G]

/-- All available proper-enlargement geometry, without the model sieve or
any conclusion about the full automorphism centralizer. The standing
`Hypothesis1611` is supplied separately to the model calculations. -/
structure PairContext (E L I : Subgroup G) (t i : G) : Prop where
  setup : ComponentTransfer.Setup t i L
  card : Nat.card E = 4
  t_mem : t ∈ E
  closure_eq : I = ComponentTransfer.layerClosure (involutionCentralizer i) L
  component : IsCentralizerComponent i I
  proper : L < I
  commutator_eq : ⁅I, zpowers t⁆ = I
  centralizes : E ≤ centralizer (L : Set G)
  centralizes_i : E ≤ involutionCentralizer i
  normalizes : E ≤ normalizer (I : Set G)
  faithful : Function.Injective (inducedAction E I normalizes)

/-- Pointwise fixation in the actual enlargement, not an abstract pair of
isomorphism types. -/
def pairFixer (L I : Subgroup G) : Subgroup (MulAut I) :=
  fixingSubgroup (MulAut I) (L.subgroupOf I : Set I)

/-- The two numerical/action facts needed to recognize the full fixer once
a faithful order-four subgroup has been embedded in it. -/
structure FourBound (L I : Subgroup G) : Prop where
  card_le : Nat.card (pairFixer L I) ≤ 4
  square : ∀ a : pairFixer L I, a ^ 2 = 1

/-- The five characteristic-two rows of 16.1.7(3a–e).
Each bound still has to be proved with the embedding from `PairContext`. -/
structure LieBounds (L I : Subgroup G) : Prop where
  field : ∀ (X : FieldFamily) (n : ℕ), 1 ≤ n →
    X.ModelAt (I ⧸ pCore 2 I) (2 ^ (2 * n)) →
    X.DerivedAt (L ⧸ pCore 2 L) (2 ^ n) → Nat.card (pairFixer L I) < 4
  graph_field_linear : ∀ n : ℕ, 1 < n →
    ClassicalGroup.IsPSL I 3 (2 ^ (2 * n)) →
    ClassicalGroup.IsPSU L 3 (2 ^ n) → Nat.card (pairFixer L I) < 4
  graph_linear_unitary : ∀ n : ℕ, 1 < n →
    (ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSU (I ⧸ pCore 2 I) 3 (2 ^ n)) →
    ClassicalGroup.IsPSL L 2 (2 ^ n) → Nat.card (pairFixer L I) < 4
  graph_field_symplectic : ∀ m : ℕ, 1 ≤ m →
    ClassicalGroup.IsPSp I 2 (2 ^ (2 * m + 1)) →
    Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      Nat.card (pairFixer L I) < 4
  graph_binary : ∀ n : ℕ, n = 4 ∨ n = 5 →
    ClassicalGroup.IsPSL I n 2 → Nonempty (L ≃* alternatingGroup (Fin 6)) →
      Nat.card (pairFixer L I) < 4

/-- Both J₂ rows, retaining the distinction between the A₅ and L₃(2)
components. Their abstract orders alone do not establish these bounds. -/
structure JankoBounds (L I : Subgroup G) : Prop where
  alternating : Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.j2.Carrier) →
    Nonempty (L ≃* alternatingGroup (Fin 5)) → FourBound L I
  linear : Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.j2.Carrier) →
    ClassicalGroup.IsPSL L 3 2 → Nat.card (pairFixer L I) < 4

def MathieuBound (L I : Subgroup G) : Prop :=
  Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.m12.Carrier) →
    Nonempty (L ≃* alternatingGroup (Fin 5)) → FourBound L I

def HigmanSimsBound (L I : Subgroup G) : Prop :=
  Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.hs.Carrier) →
    (Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 8))) → FourBound L I

def RudvalisBound (L I : Subgroup G) : Prop :=
  Nonempty ((I ⧸ pCore 2 I) ≃* SporadicName.ru.Carrier) →
    Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) → FourBound L I

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
