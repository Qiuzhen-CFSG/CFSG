module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Local
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.SymplecticFour.Flag
public import Theory.Representation.FirstCohomologySymplecticFour.Generation
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The complete output specification for E.6.8 and its E.6.11 model actions

The five alternatives retain the actual groups, their central quotients,
induced action images and embedded subgroups. A Borel is the preimage of the
Sylow-two normalizer in the specified central quotient; parabolics contain a
Borel in the given symplectic group. Roots are explicit matrix root families
transported through an isomorphism, including the action of Sp4(2) on Sp4(2)'.
The unitary parameter is the fixed-field order, and central two-covers and
alternating triple covers are retained.

These are output specifications only. No theorem constructing the five
alternatives or their torus witnesses is claimed here. The common preliminary
proofs are in `Components.Basic`; the two component sieves and the intrinsic
Borel and parabolic actions remain proof obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8 and
E.6.11, printed pp.247–250 (PDF pp.258–261). In E.6.8(1), the bar over L ∩ M
means its induced action on V. Infinity in E.6.11(3c) is the solvable residual.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components
open Chapter1.Section02.LocalModels
open Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G]

/-- The quotient dimension m(V/C_V(L)). -/
noncomputable def actionCorank (V L : Subgroup G) : ℕ :=
  subgroupCorank V (V ⊓ centralizer (L : Set G))

/-- Internal direct product, with the actual two embedded factors. -/
def DirectDecomposition (V A B : Subgroup G) : Prop :=
  A ⊔ B = V ∧ A ⊓ B = ⊥ ∧ ⁅A, B⁆ = ⊥

/-- B is the full preimage of a Borel of L/Z(L), realized as a
Sylow-two normalizer in that specific central quotient. -/
def BorelPreimage (L B : Subgroup G) : Prop :=
  B ≤ L ∧ ∃ S : Sylow 2 (L ⧸ center L),
    B.subgroupOf L = (normalizer (S : Set (L ⧸ center L))).comap
      (QuotientGroup.mk' (center L))

/-- A maximal proper parabolic containing a Borel in the specified group L. -/
def MaximalParabolic (L P : Subgroup G) : Prop :=
  P ≤ L ∧ IsCoatom (P.subgroupOf L) ∧
    ∃ S : Sylow 2 L, normalizer (S : Set L) ≤ P.subgroupOf L

/-- The matrix root family in an actual symplectic model of L. Both root
lengths are allowed; the model isomorphism, subgroup and field are linked. -/
def SymplecticRoot (L R : Subgroup G) (n : ℕ) : Prop :=
  R ≤ L ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧ ∃ e : L ≃* Sp F, ∃ r : Fin 8,
      (R.subgroupOf L).map e.toMonoidHom =
        closure (Set.range (Representation.OneCohomology.SymplecticFour.rootElement
          (K := F) r))

/-- The source Aut_V(L) root assertion uses actual conjugation on Sp4(q)'.
At q=2 a root element can lie outside the derived group; using Sp4(q)' as
the acting group would incorrectly exclude that source endpoint. -/
def SymplecticRootAction (L V : Subgroup G) (n : ℕ) : Prop :=
  V ≤ normalizer (L : Set G) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ e : L ≃* commutator (Sp F), ∃ r : Fin 8,
      ((inducedAutomizer L V).map (Automizer L).subtype).map
          (MulAut.congr e).toMonoidHom =
        (closure (Set.range (Representation.OneCohomology.SymplecticFour.rootElement
          (K := F) r))).map (MulAut.conjNormal (H := commutator (Sp F)))

/-- The small endpoint retains Sp4(2)', rather than silently replacing it
by a differently constructed A6. -/
def SymplecticDerivedModel (L : Subgroup G) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧ Nonempty (L ≃* commutator (Sp F))

/-- The four model possibilities in E.6.8(1). The last permits every central
two-cover; the unitary parameter is the fixed-field order. -/
inductive BorelComponentModel (L : Subgroup G) (n : ℕ) : Prop
  | linear_two (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m) (hn : n = 2 * m + 1)
      (iso : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | linear_three (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n))
  | unitary_three (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSU L 3 (2 ^ n))
  | linear_three_cover (hn : n = 2) (hz : IsPGroup 2 (center L))
      (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4)

/-- The characteristic-two side of the 1.1.5 list, used to split the two
independent E.6.8 sieves. It includes the small derived endpoints and central
two-covers of L3(4) and G2(4). It is an isomorphism predicate only. -/
def LieTypeComponent (L : Subgroup G) : Prop :=
  ClassificationModels.IsBenderModel L ∨ RankTwoTheoremC L ∨
    ClassicalGroup.IsPSL L 4 2 ∨ ClassicalGroup.IsPSL L 5 2 ∨
    (IsPGroup 2 (center L) ∧
      (ClassicalGroup.IsPSL (L ⧸ center L) 3 4 ∨
        ClassificationModels.IsG2At (L ⧸ center L) 4))

structure BorelAlternative (M V U L : Subgroup G) (n : ℕ) : Prop where
  model : BorelComponentModel L n
  borel : BorelPreimage L (L ⊓ M)
  action : Nonempty (inducedAutomizer V (L ⊓ M) ≃* Multiplicative (ZMod (2 ^ n - 1)))
  dimension : n = actionCorank V L
  bound : n ≤ subgroupCorank V U
  decomposition : 1 < n → DirectDecomposition V ⁅V, L ⊓ M⁆ (V ⊓ centralizer (L : Set G))
  displacement_dimension : 1 < n → subgroupCorank ⁅V, L ⊓ M⁆ ⊥ = n

structure SymplecticAlternative (M V U L : Subgroup G) (n : ℕ) : Prop where
  model : SymplecticDerivedModel L n
  bound : actionCorank V L ≤ subgroupCorank V U
  decomposition : 1 < n → DirectDecomposition V ⁅V, L ⊓ M⁆ (V ⊓ centralizer (L : Set G))
  local_structure :
    (BorelPreimage L (L ⊓ M) ∧
      ((actionCorank V L = 2 * n ∧ ∃ A : Subgroup G, U < A ∧ A < V ∧
        subgroupCorank V A = n ∧ ¬ L ⊓ centralizer (A : Set G) ≤ M) ∨
       (IsAlternating L 6 ∧ actionCorank V L = 1))) ∨
    (MaximalParabolic L (L ⊓ M) ∧ SymplecticRootAction L V n ∧ actionCorank V L = n)

structure LinearFourAlternative (M V U Q L : Subgroup G) : Prop where
  model : ClassicalGroup.IsPSL L 4 2
  quotient : Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8))
  fixed : U = V ⊓ centralizer (L : Set G)
  dimension : actionCorank V L = 1
  global_rank : globalR V = 1

structure AlternatingAlternative (M V U L : Subgroup G) : Prop where
  model : IsAlternating L 7 ∨ IsAlternatingCover L 6 ∨ IsAlternatingCover L 7
  escape : ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ subgroupCorank V A = 1 ∧
    ¬ L ⊓ centralizer (A : Set G) ≤ M
  global_rank : globalR V = 1
  dimension : actionCorank V L ≤ 2

structure OddAlternative (M V U L : Subgroup G) : Prop where
  model : (∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
    ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)
  fixed : U = V ⊓ centralizer (L : Set G)
  dimension : actionCorank V L = 1
  global_rank : globalR V = 1

/-- Every clause of E.6.8, as an output specification, not an asserted theorem. -/
def ComponentAlternatives (M V U Q L : Subgroup G) : Prop :=
  (∃ n, BorelAlternative M V U L n) ∨
  (∃ n, SymplecticAlternative M V U L n) ∨
  LinearFourAlternative M V U Q L ∨ AlternatingAlternative M V U L ∨
  OddAlternative M V U L

/-- Regularity of the actual conjugation action on W minus its identity. -/
def RegularConjugation (X W : Subgroup G) : Prop :=
  X ≤ normalizer (W : Set G) ∧ ∀ a ∈ W, a ≠ 1 → ∀ b ∈ W, b ≠ 1 →
    ∃! x : X, (x : G) * a * (x : G)⁻¹ = b

/-- The common torus output needed by E.6.11. Complement and action clauses
refer to the actual embedded subgroups. -/
structure TorusAction (M V L X : Subgroup G) (n : ℕ) : Prop where
  le_intersection : X ≤ L ⊓ M
  cyclic : Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1)))
  complement : (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M
  disjoint : (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥
  displacement : ⁅V, X⁆ = ⁅V, L ⊓ M⁆
  regular : RegularConjugation X ⁅V, X⁆

/-- Intrinsic Borel output, retaining the central two-cover. -/
def BorelTorusConclusion (M V Q L : Subgroup G) (n : ℕ) : Prop :=
  ∃ X : Subgroup G, TorusAction M V L X n ∧
    L.pCoreIn 2 ⊔ ⁅V, X⁆ = (center ↥(L ⊓ Q)).map (L ⊓ Q).subtype

/-- Intrinsic parabolic output: infinity means the solvable residual. -/
def ParabolicTorusConclusion (M V L : Subgroup G) (n : ℕ) : Prop :=
  ∃ X : Subgroup G, TorusAction M V L X n ∧ SymplecticRoot L ⁅V, X⁆ n ∧
    (solvableResidual ↥(L ⊓ M)).map (L ⊓ M).subtype = L ⊓ centralizer (V : Set G)

end CFSG.Quasithin.ChapterE.Section06.Components
