module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Semisimple.BinaryThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Completion.MarkedRows
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.ThompsonComparison

/-!
# Original survivor assembly from small quiet component quotients

The binary-three input is now an actual component equivalence and a bound
on the literal moved central quotient, with no irreducibility or natural
marking premise. Clifford restriction and the small-module classification
construct the marking. Local Thompson centralization transports through
contained reselection by its proved full-module form. The existing row
exclusions and terminal TI argument then supply the survivor and w≥2.

This remains conditional assembly. Constructing the remaining quiet rows
stays with qt-d-10-nona5-small-offender. HalfSylowUniqueAt retains producer
qt-d-10-nona5-half-sylow-unique and final discharge by
qt-d-10-nona5-point-control. No unconditional source recognition is claimed.
Source: Aschbacher–Smith 10.1.1 and10.2.12, pp.741,754–755.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Subgroup Theory.GroupTheory Representation
open Chapter3.Section02 PointControl.Selection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Original survivor assembly from an unmarked small binary-three quotient
or the remaining concrete quiet rows. No binary-three irreducibility is assumed. -/
theorem nonnormalSmallOffender_of_quiet_small_quotients_and_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hquiet : ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
      Configuration T D g →
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) →
      ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
        E.fullModule ≤ D.fullModule ∧
        ((Nonempty ((L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group) ∧
            (centralizer (L : Set G)).relIndex ⁅E.fullModule,L⁆ < 512) ∨
          RankOneNatural E ∨ NaturalDualRow E ∨ FourNaturalRow E ∨
          OrthogonalFourMinusRow E ∨ SuzukiNaturalRow E)) :
    SourceNonnormalSmallOffenderAt T := by
  apply nonnormalSmallOffender_of_quiet_marked_rows_and_halfSylow hhalf
  intro L D g c hJ
  obtain ⟨E,hE,hrow⟩ := hquiet L D g c hJ
  refine ⟨E,hE,?_⟩
  rcases hrow with ⟨⟨e⟩,hsmall⟩ | hrow
  · obtain ⟨he,cE⟩ := c.reselect E hE
    have hthree : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
      decide
    have hJE : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (E.moduleSubgroup : Set G) :=
      (ModuleChoice.full_thompson_centralizes_of_local_three D c.nonnormal hthree hJ).trans
        (centralizer_le ((le_componentOrbit _ _).trans hE))
    exact Or.inl (natural_of_quiet_binary_three_small_quotient E cE hJE
      (PointControl.component_normalizer_le_of_halfSylowUnique E cE.nonnormal
        (hhalf cE.many L E cE.nonnormal cE.notA5)) e hsmall)
  · exact Or.inr hrow
end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
