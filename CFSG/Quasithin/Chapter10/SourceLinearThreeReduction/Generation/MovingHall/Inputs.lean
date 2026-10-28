module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Contracts
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Borel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceMovement.OriginalSetup
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SL2.BinarySmallModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Source interfaces for the general-field moving-center branch

`Context` contains exactly the hypotheses of `SourceNonnormalMovingHallAt`.
The three subsequent predicates are unproved source obligations, not chapter
results. They separate row selection, actual Hall placement, and the geometric
construction of the terminal overcomponent. Every module assertion specifies
the original moved section and its literal quotient action. The terminal
configuration retains an axis of the original Hall, the Baumann commutator,
and the actual normalizer of their Borel. Final assembly must discharge all
three obligations before the source Hall contract is established.

Source: Aschbacher--Smith 10.1.1--2 and 10.2.1--3, pp.741--747. The last
predicate includes the original component, Cartan-axis, and block arguments
on pp.746--747; it is not supplied by the field-four A₅ theorem.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Only the source hypotheses, with faithfulness on the two-core quotient. -/
structure Context (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) : Prop where
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  minimal : D.IsMinimalFullModule
  nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)
  not_a5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal
  large : 1 < generationParameter H
  moving : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥
  hall_le : B ≤ D.maximalLocal.subgroupOf H
  hall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))
  abelian : IsMulCommutative B
  permutes : (B.map H.subtype : Set G) * (T : Set G) =
    (T : Set G) * (B.map H.subtype : Set G)
  faithful : B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
variable {F : Type} [Field F] [Finite F] [CharP F 2]
local instance naturalMarkingAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Case (1) of 10.1.1, on the actual moved section, with the crossed action. -/
def NaturalMarking (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) : Prop :=
  Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) ∧
    ∃ t : G, t ∈ T ∧ t ∉ normalizer (L : Set G) ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)

/-- Moving-center module selection, after removing the genuine SL₃(2) row. -/
def NaturalRowAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H), Context D H B →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,F), NaturalMarking D e

/-- Source pp.745--746: eliminate the field factor and place the original B. -/
def NaturalHallPlacementAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H), Context D H B →
    ∀ (n : ℕ), 1 < n →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 ^ n →
    ∀ e : (L ⧸ pCore 2 L) ≃* SL(2,F), NaturalMarking D e →
      B.map H.subtype ≤ sourceOrbitBorel T L

/-- The actual terminal configuration, before the independent odd-rank step.
The axis belongs to the original Hall, and its two-part is the prescribed
Baumann commutator. All normality here is inside the displayed normalizer. -/
structure TerminalConfiguration (T : Sylow 2 G) (L C : Subgroup G) (n : ℕ) where
  axis : Subgroup G
  overcomponent : Subgroup G
  axis_le_hall : axis ≤ C
  axis_le_orbit : axis ≤ localOrbit T L
  axis_original : axis ≤ L ∨ ∃ t : G, t ∈ T ∧
    t ∉ normalizer (L : Set G) ∧ axis ≤ L.map (MulAut.conj t).toMonoidHom
  axis_card : Nat.card axis = 2 ^ n - 1
  faithful : axis ⊓ centralizer
    ((⁅ChapterB.baumann (T : Subgroup G), axis⁆ : Subgroup G) : Set G) = ⊥
  local_sqtk : IsSQTK KnownSimple.IsKnownSimple
    (normalizer ((⁅ChapterB.baumann (T : Subgroup G), axis⁆ ⊔ axis : Subgroup G) : Set G))
  component : overcomponent ∈ Chapter1.cComponentsIn
    (normalizer ((⁅ChapterB.baumann (T : Subgroup G), axis⁆ ⊔ axis : Subgroup G) : Set G))
  model : IsSL overcomponent 3 (2 ^ n) ∨ ClassicalGroup.IsPSL overcomponent 3 (2 ^ n)
  centralizes : overcomponent ≤ centralizer
    ((⁅ChapterB.baumann (T : Subgroup G), axis⁆ ⊔ axis : Subgroup G) : Set G)

/-- Source pp.746--747: original blocks, Cartan axes and terminal overcomponent. -/
def NaturalTerminalAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H), Context D H B →
    ∀ (n : ℕ), 1 < n →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 ^ n →
    ∀ e : (L ⧸ pCore 2 L) ≃* SL(2,F), NaturalMarking D e →
      B.map H.subtype ≤ sourceOrbitBorel T L →
      Nonempty (TerminalConfiguration T L (B.map H.subtype) n)

end CFSG.Quasithin.Chapter10.MovingHall
