module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.OddCoreGeneration
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Component contracts for the E.6.18–19 argument

Components are ordinary quasisimple components of the indicated centralizer,
not ambient normal subgroups. The exceptional models are the existing actual
A₇ isomorphism and perfect central three-cover predicates.

The two lifting contracts isolate the use of I.3.1, inspection of Theorem C,
and uniqueness from A.3.18. The odd-core contract isolates the obstruction
obtained from Aschbacher 31.14(1), 31.18 and inspection of E.6.8: failure of
balance across an index-two subspace produces an exceptional component.
These are definitions of outstanding mathematical obligations, not theorems.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18–19,
printed p.252 (PDF p.263); I.3.1, printed pp.414–415; A.3.18, pp.51–52.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance

variable {G : Type*} [Group G]

/-- Ordinary component membership relative to C_G(U), with its actual inclusion. -/
def CentralizerComponent (U L : Subgroup G) : Prop :=
  L ≤ centralizer (U : Set G) ∧
    IsComponent (centralizer (U : Set G)) (L.subgroupOf (centralizer (U : Set G)))

/-- A₇ or its perfect central three-cover, using the established model predicates. -/
def IsSeven (L : Subgroup G) : Prop :=
  Chapter1.Section02.LocalModels.IsAlternating L 7 ∨
    Chapter1.Section02.LocalModels.IsAlternatingCover L 7

/-- The exact escaping-hyperplane clause of E.6.8(4), specialized to its
A₇ and three-cover cases. This is an earlier-source input to E.6.18. -/
def SevenEscape (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, ∀ L : Subgroup G,
    CentralizerComponent U L → IsSeven L →
      ∃ W : Subgroup G, IsHyperplane V W ∧ U ≤ W ∧
        ¬ L ⊓ centralizer (W : Set G) ≤ M

/-- The I.3.1/model-inspection step: an exceptional centralizer component
survives passage to the centralizer of a smaller nonidentity subspace. -/
def SevenLifting (V : Subgroup G) : Prop :=
  ∀ A U L : Subgroup G, A ≤ U → U ≤ V → A ≠ ⊥ →
    CentralizerComponent U L → IsSeven L → CentralizerComponent A L

/-- The consequence of A.3.18 for two exceptional components of the same
nonidentity subspace centralizer. No normality in G is asserted. -/
def SevenUniqueness (V : Subgroup G) : Prop :=
  ∀ A : Subgroup G, A ≤ V → A ≠ ⊥ → ∀ L J : Subgroup G,
    CentralizerComponent A L → CentralizerComponent A J →
      IsSeven L → IsSeven J → L = J

/-- The E.6.19 obstruction, before E.6.18 excludes its output. In the source
the quotient is C_G(A)/(O(C_G(A)) A), and U/A has order two. A proof must
construct that quotient and lift the detected component back to C_G(A). -/
def OddCoreObstruction (M V : Subgroup G) : Prop :=
  ∀ A ∈ obstructionFamily M V, subgroupCorank V A = 2 → ∀ U : Subgroup G,
    A ≤ U → U ≤ V → A.relIndex U = 2 →
      (¬ oddCentralizer U ≤ oddCentralizer A) →
        ∃ L : Subgroup G, CentralizerComponent A L ∧ IsSeven L

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
