module
public import Theory.Representation.PSL3Two.FourNaturalRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.AllIntersections

/-!
# The four-natural-copy row with a small offender

The literal moved central quotient has dimension twelve. Its full linear
normalizer has two-rank at most nine, so the full induced local action has
all large-row bounds. The uniform fixed-space argument excludes the actual
small offender, also after contained seed reselection.

Crossed centralization is an explicit premise from the source row selector;
it is not implied by the four-copy marking alone. Its discharge and the
remaining quiet recognition stay with qt-d-10-nona5-small-offender.
Source: Aschbacher--Smith 10.1.1(6) and 10.2.12, pp.741,754--755.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal central quotient consists of four identically marked natural SL₃(2) copies. -/
def FourNaturalRow (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.FourNatural.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

theorem four_natural_large_bounds
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : FourNaturalRow D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    Nonempty (LargeModuleBounds D) := by
  obtain ⟨e,⟨c⟩⟩ := hrow
  apply large_bounds_of_marked_normalizer D BinaryLinearThree.FourNatural.action e c hn hcross
    (m := 12) (r := 9) (by decide) ?_
    BinaryLinearThree.FourNatural.linearNormalizer_two_rank_le_nine (by decide)
  norm_num [BinaryLinearThree.FourNatural.Space,BinaryLinearThree.Vector,Nat.card_fun]

theorem no_four_natural_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hrow : FourNaturalRow D)
    (hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨b⟩ := four_natural_large_bounds D hrow c.nonnormal hcross
  exact FixedSpaces.large_module_false_of_normalizer D c b hNL

theorem no_contained_four_natural_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (E : FundamentalSetup KnownSimple.IsKnownSimple T L) (hE : E.fullModule ≤ D.fullModule)
    (hrow : FourNaturalRow E)
    (hcross : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅E.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨he,cE⟩ := c.reselect E hE
  exact no_four_natural_of_small_offender E cE hrow hcross hNL

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
