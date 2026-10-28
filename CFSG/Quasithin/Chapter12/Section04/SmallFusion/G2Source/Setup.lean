module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerModelBounds
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Setup

/-!
# The fixed-involution setup for the original binary G₂ Weyl row

The seven-dimensional Weyl marking first descends through the scalar-line
cover to the literal central quotient.  The binary natural dual has
one-dimensional first cohomology, so a nonzero fixed subgroup of the chosen
module has exactly two elements.  The generic 12.4.3 setup then supplies its
involutory generator and the centralizer/normalizer equalities.

This is only the fixed-cardinality/setup part of the original G₂ branch.  The
remaining 12.4.7--12.4.9 fusion and commutator argument is kept separate.
Source: Aschbacher--Smith 12.4.2--3, pp.812--813, together with 12.2.2(3f)
and the binary Weyl cover at 12.2.16, pp.795, 799--800.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02
open Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Chapter12.Section04.SmallFusion
open Chapter12.Section04.SmallFusion.SLThreeSource.At
open ChapterB.QuasisimpleSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

local notation "F" => ZMod 2

/-- The Weyl marking on `V` descends to the literal central quotient. -/
private noncomputable def central_model
    (D : ChosenModule T L V)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action F)) :
    ActionEquiv D.centralQuotientAction
      (g2DerivedNatural F) := by
  let p := Atlas.G2.Natural.OrthogonalCover.projection F
  have hp := Atlas.G2.Natural.OrthogonalCover.projection_isCover F
  exact chosenCentralEquiv_of_cover D e p hp.1
    (by
      rw [Atlas.G2.Natural.OrthogonalCover.projection_ker,
        Atlas.G2.Natural.OrthogonalCover.fixed_eq_scalarLine])

/-- A nonzero fixed subgroup in the Weyl row is a single involution. -/
theorem fixed_card_eq_two
    (D : ChosenModule T L V)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    Nat.card (V ⊓ centralizer (L : Set G) : Subgroup G) = 2 := by
  exact ChosenCover.fixed_card_eq_two D (central_model D e) hne
    Atlas.G2.Natural.BinarySylowFixedSpace.derived_natural_dual_H1_finrank.le

/-- The original 12.4.3 setup for a nonzero fixed binary G₂ Weyl module. -/
theorem exists_fixed_involution_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    ∃ z : G, orderOf z = 2 ∧
      V ⊓ centralizer (L : Set G) = zpowers z ∧
      normalizer (L : Set G) = centralizer ({z} : Set G) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) ∧
      centralizer (omegaOneAmbient ((center (T : Subgroup G)).map
        (T : Subgroup G).subtype) : Set G) ≤ normalizer (L : Set G) := by
  exact SLThreeSource.At.exists_fixed_involution_setup_of_card_two h D structural
    SLThreeSource.uniquenessEarlier_knownSimple
    (fixed_card_eq_two D e hne)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
