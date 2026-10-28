module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Scalar
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.AllIntersections
public import Theory.Representation.Suzuki.NaturalNormalizerRank

/-!
# The Suzuki natural row with a small offender

The marked moved quotient has dimension 4(2m+1); its full binary normalizer
has two-rank at most 2m+1. Perfectness of the opposite component and the
scalar commutant prove crossed centralization. These facts supply all local
bounds, and the original uniform fixed-space argument excludes the offender.
The exclusion also applies after contained seed reselection.

The source row selector remains with qt-d-10-nona5-small-offender. The
normalizer bound N_G(L) ≤ M retains the existing half-Sylow producer, with
ultimate discharge by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.1.1(7) and 10.2.12, pp.741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

@[expose] def SuzukiNaturalRow (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m,
    Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      ((SuzukiNatural.natural m).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

theorem suzuki_crossed_of_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : SuzukiNaturalRow D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  obtain ⟨m,hm,e,⟨c⟩⟩ := hrow
  exact crossed_of_scalar_commutant D (SuzukiNatural.natural m) e c
    (fun f hf => SuzukiNatural.commuting_addHom_eq_scalar m f.toAddMonoidHom hf) ht htn

theorem suzuki_large_bounds
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : SuzukiNaturalRow D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty (LargeModuleBounds D) := by
  obtain ⟨m,hm,e,⟨c⟩⟩ := hrow
  apply large_bounds_of_marked_normalizer D (SuzukiNatural.natural m) e c hn
    (fun t ht htn => suzuki_crossed_of_marking D ⟨m,hm,e,⟨c⟩⟩ ht htn)
    (m := 4*(2*m+1)) (r := 2*m+1) (by omega) ?_
    (SuzukiNatural.natural_normalizer_rank m hm) (by omega)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,SuzukiNatural.natural_finrank]

theorem no_suzuki_natural_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hrow : SuzukiNaturalRow D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨b⟩ := suzuki_large_bounds D hrow c.nonnormal
  exact FixedSpaces.large_module_false_of_normalizer D c b hNL

theorem no_contained_suzuki_natural_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (E : FundamentalSetup KnownSimple.IsKnownSimple T L) (hE : E.fullModule ≤ D.fullModule)
    (hrow : SuzukiNaturalRow E)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨he,cE⟩ := c.reselect E hE
  exact no_suzuki_natural_of_small_offender E cE hrow hNL

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
