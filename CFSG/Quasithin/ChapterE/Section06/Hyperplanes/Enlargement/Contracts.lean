module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Mathlib.Data.Set.Card

/-!
# The remaining enlargement obligations in E.6.22–23

These contracts separate the two model inspections from the bound on the
actual conjugacy family. They assert no theorem. Components and blocks are
relative to the indicated centralizer; the alternating block types include
their actual conjugation modules. The A₅-in-A₇ exception retains both model
identifications. The earlier E.6.10 input selects an actual escaping block.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.253–255 (PDF pp.264–266). The owner `Hyperplanes.Enlargement` must discharge
the new lifting, block and orbit contracts before completing its conditional
enlargement implication. E.6.18 and E.6.21 remain inputs to that implication.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
open ComponentBalance

variable {G : Type*} [Group G]

/-- The exact earlier E.6.18 exclusion, for the source family Γ. -/
def SevenExcluded (M V : Subgroup G) : Prop :=
  ∀ A ∈ obstructionFamily M V, subgroupCorank V A ≤ 2 →
    ∀ L : Subgroup G, CentralizerComponent A L → ¬ IsSeven L

/-- The exact E.6.21 conclusion, with the odd core computed intrinsically. -/
def OddCoreFree (V : Subgroup G) : Prop :=
  ∀ A : Subgroup G, A ≤ V → A ≠ ⊥ → pPrimeCore 2 (centralizer (A : Set G)) = ⊥

/-- An actual A₃ or A₅ block of C_G(U), including relative subnormality. -/
def SmallBlock (U L : Subgroup G) : Prop :=
  L ≤ centralizer (U : Set G) ∧
    ChapterC.IsBlock (L.subgroupOf (centralizer (U : Set G))) ∧
      (ChapterC.IsAlternatingBlock L 3 ∨ ChapterC.IsAlternatingBlock L 5)

/-- The selection consequence used from earlier E.6.10(1) and E.6.10(2).
The source decomposition supplies a factor since C_G(U) escapes M. -/
def EarlierBlockSelection (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) →
      ∃ L : Subgroup G, SmallBlock U L ∧ ¬ L ≤ M

/-- I.3.1 and the two-central model inspection in E.6.22, before excluding
the A₅-in-A₇ exception. Both centralizers and their inclusions are retained. -/
def ComponentLiftAlternative (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, CentralizerComponent U L →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A ≤ 2 →
        ∃ X : Subgroup G, L ≤ X ∧ CentralizerComponent A X ∧
          (L = X ∨ Chapter1.Section02.LocalModels.IsAlternating L 5 ∧ IsSeven X)

/-- The commuting-conjugate alternative refers to the actual M_V action. -/
def CommutingConjugates (M V L : Subgroup G) : Prop :=
  ∀ g ∈ localNormalizer M V,
    L = L.map (MulAut.conj g).toMonoidHom ∨
      ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥

/-- The actual conjugacy family, not an abstract set of factor labels. -/
def conjugates (M V L : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : localNormalizer M V => L.map (MulAut.conj (g : G)).toMonoidHom

/-- The missing local application of 1.2.1(3), common to components and
blocks. Commutativity by itself does not bound the number of factors. -/
def TwoConjugates (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, (CentralizerComponent U L ∨ SmallBlock U L) →
      (¬ L ≤ M) → CommutingConjugates M V L → (conjugates M V L).ncard ≤ 2

/-- The surviving proper-enlargement configuration on p.254. The model is
an actual A₆ isomorphism, and normality is inside C_X(U), not inside G. -/
structure ProperSixEnlargement (V U A L X : Subgroup G) : Prop where
  proper : L < X
  component : CentralizerComponent A X
  model : Chapter1.Section02.LocalModels.IsAlternating X 6
  fixed : V ⊓ centralizer (X : Set G) = A
  normal_in_centralizer : (L.subgroupOf (X ⊓ centralizer (U : Set G))).Normal

/-- The further-enlargement obligation through a nonidentity corank-three
centralizer. Its proof must identify the actual L₄(2)/L₅(2) model and the
outer and two-central automorphisms. Only containment of each conjugate is
needed by the fixed-space contradiction; equality with their join is not
assumed. This may be supplied independently of the initial A₆ reduction. -/
def SixOrbitContainment (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      ∀ A ∈ obstructionFamily M V, A ≤ U → subgroupCorank V A = 2 →
        ∀ X : Subgroup G, ProperSixEnlargement V U A L X →
          ∀ g ∈ localNormalizer M V, L.map (MulAut.conj g).toMonoidHom ≤ X

/-- The block enlargement obligation on pp.254–255, after E.6.22 has been
proved. A proof must establish equality with the enlarged blocks, by ruling
out proper L₂(4)-block enlargement and then the A₆ component case, including
the further L₄(2)/L₅(2) automorphism calculation. This is not an earlier input. -/
def BlockEnlargement (M V : Subgroup G) : Prop :=
  ∀ U ∈ obstructionFamily M V, IsHyperplane V U →
    ∀ L : Subgroup G, SmallBlock U L → (¬ L ≤ M) →
      CommutingConjugates M V L

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
