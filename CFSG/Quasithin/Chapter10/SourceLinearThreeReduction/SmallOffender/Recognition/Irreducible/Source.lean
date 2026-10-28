module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Irreducible.BinaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Completion.MarkedRows

/-!
# Source assembly with unmarked irreducible binary-three quotients

The quiet selector may supply the literal binary-three quotient and its
irreducibility. Recognition constructs its natural marking and applies the
original survivor consumer, including after contained reselection.

This is conditional assembly. The quiet classification remains in
qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains producer
qt-d-10-nona5-half-sylow-unique and final discharge by
qt-d-10-nona5-point-control. No unconditional quiet selection is asserted.
Source: Aschbacher–Smith 10.1.1 and 10.2.12, printed pp.741,754–755.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Original survivor assembly with binary-three naturality replaced by irreducibility
of its literal moved quotient; all other row bounds are already proved. -/
theorem nonnormalSmallOffender_of_quiet_irreducible_rows_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ (E : FundamentalSetup KnownSimple.IsKnownSimple T L)
        (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)),
        E.fullModule ≤ D.fullModule ∧
        ((∃ e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
            letI := source_full_moved_elementary E
            (binaryThreeMovedAction E hn e).IsIrreducible) ∨
          RankOneNatural E ∨ NaturalDualRow E ∨ FourNaturalRow E ∨
          OrthogonalFourMinusRow E ∨ SuzukiNaturalRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_marked_rows_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hn,hE,hrow⟩ := hquiet L D g c hJ
  refine ⟨E,hE,?_⟩
  rcases hrow with ⟨e,hi⟩ | hrow
  · obtain ⟨he,cE⟩ := c.reselect E hE
    exact Or.inl (natural_of_binary_three_moved_irreducible E e cE
      (PointControl.component_normalizer_le_of_halfSylowUnique E cE.nonnormal
        (hhalf cE.many L E cE.nonnormal cE.notA5)) hi)
  · exact Or.inr hrow

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
