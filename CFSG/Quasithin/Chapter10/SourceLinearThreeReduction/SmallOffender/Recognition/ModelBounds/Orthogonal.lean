module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Scalar
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.AllIntersections
public import Theory.Representation.OrthogonalFourMinusRankOne.NormalizerRank

/-!
# The minus-type orthogonal row with a small offender

The literal Hermitian four-space over GF(2^n) is acted on by the actual
SL₂(2^(2n)) quotient. Its binary dimension is 4n and its full normalizer
has two-rank at most 2n. The scalar commutant and perfect opposite component
supply crossed centralization, including the original fixed kernel.
For n>1 these bounds exclude the original offender, also after reselection.

The remaining row selection belongs to qt-d-10-nona5-small-offender.
N_G(L) ≤ M retains the half-Sylow source producer and ultimate discharge by
qt-d-10-nona5-point-control. The marking is a hypothesis, not a classification.
Source: Aschbacher--Smith 10.1.1(4) and 10.2.12, pp.741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

@[expose] def OrthogonalFourMinusRow (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n), 1 < n ∧
    letI : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
    letI : Module (ZMod 2) (Space n) :=
      Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))
    ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,Field n),
      Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆
        (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
        ((SL2.BinarySmall.hermitian n).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

theorem orthogonal_crossed_of_marking
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : OrthogonalFourMinusRow D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  obtain ⟨n,hn0,hn,e,⟨c⟩⟩ := hrow
  let : NeZero n := hn0
  let : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
  let : Module (ZMod 2) (Space n) :=
    Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))
  exact crossed_of_scalar_commutant D (SL2.BinarySmall.hermitian n) e c
    (OrthogonalFourMinus.RankOne.AmbientActions.commuting_binaryEnd_eq_scalar n) ht htn

theorem orthogonal_large_bounds
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hrow : OrthogonalFourMinusRow D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty (LargeModuleBounds D) := by
  obtain ⟨n,hn0,hlarge,e,⟨c⟩⟩ := hrow
  let : NeZero n := hn0
  let : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
  let : Module (ZMod 2) (Space n) :=
    Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))
  apply large_bounds_of_marked_normalizer D (SL2.BinarySmall.hermitian n) e c hn
    (fun t ht htn => orthogonal_crossed_of_marking D ⟨n,hn0,hlarge,e,⟨c⟩⟩ ht htn)
    (m := 4*n) (r := 2*n) (by omega) ?_
    (OrthogonalFourMinus.RankOne.hermitian_normalizer_rank n) (by omega)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    OrthogonalFourMinus.RankOne.space_binary_finrank]

theorem no_orthogonal_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g) (hrow : OrthogonalFourMinusRow D)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨b⟩ := orthogonal_large_bounds D hrow c.nonnormal
  exact FixedSpaces.large_module_false_of_normalizer D c b hNL

theorem no_contained_orthogonal_of_small_offender
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) {g : G}
    (c : Configuration T D g)
    (E : FundamentalSetup KnownSimple.IsKnownSimple T L) (hE : E.fullModule ≤ D.fullModule)
    (hrow : OrthogonalFourMinusRow E)
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal) : False := by
  obtain ⟨he,cE⟩ := c.reselect E hE
  exact no_orthogonal_of_small_offender E cE hrow hNL

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
