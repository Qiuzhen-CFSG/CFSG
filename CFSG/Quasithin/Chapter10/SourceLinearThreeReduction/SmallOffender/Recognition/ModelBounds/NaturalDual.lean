module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Crossed
public import Theory.Representation.PSL3Two.NaturalDualRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.AllIntersections

/-!
# Exclusion of the natural-plus-dual small-offender row

This is the actual six-dimensional natural-plus-dual representation of
SL₃(2), marked on [V,L]/C_[V,L](L). Its trivial invertible commutant gives
crossed centralization and its full normalizer has two-rank at most three.
These are the sufficient large-row bounds for the uniform fixed-space
contradiction, including after a contained minimal seed is reselected.

Source: Aschbacher--Smith 10.1.1(5) and 10.2.12, pp.741,754--755.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal central quotient carries the actual natural-plus-dual SL₃(2) action. -/
def NaturalDualRow (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.NaturalDual.action.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

theorem natural_dual_crossed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : NaturalDualRow D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  obtain ⟨e,⟨c⟩⟩ := hrow
  exact crossed_of_trivial_commutant D _ e c BinaryLinearThree.NaturalDual.centralizer_eq_one ht htn

theorem natural_dual_large_bounds
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : NaturalDualRow D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty (LargeModuleBounds D) := by
  obtain ⟨e,⟨c⟩⟩ := hrow
  let : Finite BinaryLinearThree.NaturalDual.Space := Module.finite_of_finite (ZMod 2)
  apply large_bounds_of_marked_normalizer D BinaryLinearThree.NaturalDual.action e c hn
    (fun _ ht htn => natural_dual_crossed D ⟨e,⟨c⟩⟩ ht htn)
    (m := 6) (r := 3) (by decide) ?_
    BinaryLinearThree.NaturalDual.linearNormalizer_two_rank_le_three (by decide)
  let E := (LinearEquiv.refl (ZMod 2) BinaryLinearThree.Vector).prodCongr
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm.toLinearEquiv
  rw [Nat.card_congr E.toEquiv]
  norm_num [BinaryLinearThree.Vector,Nat.card_prod,Nat.card_fun]

theorem no_natural_dual_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hrow : NaturalDualRow D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨b⟩ := natural_dual_large_bounds D hrow c.nonnormal
  exact FixedSpaces.large_module_false_of_normalizer D c b hNL

theorem no_contained_natural_dual_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (E : FundamentalSetup KnownSimple.IsKnownSimple T L) (hE : E.fullModule ≤ D.fullModule)
    (hrow : NaturalDualRow E)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨he,cE⟩ := c.reselect E hE
  exact no_natural_dual_of_small_offender E cE hrow hNL

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
