module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PinnedPositive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.CoordinatesApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootLocalCover

/-!
# Source rank-one pinnings on both original marked endpoints

The actual rank-one panel projection is faithful, and the previously chosen
simple-root parameter extends to a whole SL₂ isomorphism. Pull this map back
through each endpoint of the supplied original or geometric amalgam marking.
The resulting squares hold on every matrix element; in the original quotient
they use Q.q itself. No perfectness assumption is made, so F₂ is retained.

The positive application now uses the constructed short rank-one map and its
proved root interchanges. The original common Sylow and both endpoint formulas
are unchanged. It still requires alignment of the short Weyl image with the
source lift, the orthogonal-root centralizer, and the lower positive equations.
These are obligations for the source-family owner, not consequences of the
local PSL₂ isomorphisms. Full Borel--Weyl relations are not established here.

Source: Fong--Seitz II §7 and (9.6), (9.9)--(9.21), printed pp.192,
212--217. The earlier radical-kernel and local-group inputs remain with their
existing source producers; the final source assembly must discharge them.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.PinningPositive
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

/-- The whole rank-one map on either original or geometric marked endpoint. -/
def originalPinning (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    SL2 F ≃* MarkedLocal.originalRankOne Q e split i :=
  (sourcePinning Q split i hV μ).trans (MarkedLocal.originalRankOneEquiv Q e split i).symm

/-- The pinning square commutes on every SL₂ element at both endpoints. -/
theorem originalPinning_endpoint (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (g : SL2 F) :
    MarkedLocal.endpointMap Q e i (originalPinning Q split e i hV μ g) =
      sourcePinningHom Q split i hV μ g := by
  rw [← MarkedLocal.originalRankOneEquiv_apply]
  change ((MarkedLocal.originalRankOneEquiv Q e split i)
    ((MarkedLocal.originalRankOneEquiv Q e split i).symm
      (sourcePinning Q split i hV μ g)) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- No perfectness premise is required for the original root-panel projection. -/
theorem originalRootProjection_injective (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) :
    Function.Injective (MarkedLocal.originalRootProjection Q e split i) := by
  intro a b hab
  apply (MarkedLocal.originalRankOneEquiv Q e split i).injective
  apply rankOne_projection_injective Q split i hV μ
  apply Subtype.ext
  have he := congrArg Subtype.val hab
  rw [MarkedLocal.originalRootProjection_apply, MarkedLocal.originalRootProjection_apply] at he
  simpa only [RootLocalCover.projection_apply] using he

variable (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)
  (hs : pinnedReflection Q split short (hK short) (μ short) = (n short).val)
  (hc : rankOne Q split short ≤ centralizer (positiveCarrier Q split short 0 : Set (X ⧸ Q.D)))
  (d : PartialPositiveData (sourceRoots Q split hK μ n short))
  (h : HypothesisF11 L S)

/-- The literal positive consumer now uses the constructed short rank-one map. -/
def sourceSylowHom : Atlas.G2.unipotent (K := F) →* S :=
  CoordinatePositive.sourceSylowHom Q split hm hK μ n short d
    (sourceShortRankOne Q split hK μ n short hs hc) e h

theorem sourceSylowHom_surjective :
    Function.Surjective (sourceSylowHom Q split e hm hK μ n short hs hc d h) :=
  CoordinatePositive.sourceSylowHom_surjective Q split hm hK μ n short d
    (sourceShortRankOne Q split hK μ n short hs hc) e h

/-- The same source root parameters occur through the original common-Sylow map. -/
theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := F)) :
    MarkedLocal.sylowMap Q e h (sourceSylowHom Q split e hm hK μ n short hs hc d h u) =
      (sourceRoots Q split hK μ n short).unipotentHom
        (source_positive_relations Q split hK μ n short hs hc d).collection u :=
  CoordinatePositive.sourceSylowHom_quotient Q split hm hK μ n short d
    (sourceShortRankOne Q split hK μ n short hs hc) e h u

/-- Both endpoint representatives are retained, for either short/long orientation. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (a : Fin 6 → F) :
    let s := sourceSylowHom Q split e hm hK μ n short hs hc d h (Atlas.G2.unipotentEquiv a)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        (sourceRoots Q split hK μ n short).product a :=
  CoordinatePositive.sourceSylowHom_endpoint Q split hm hK μ n short d
    (sourceShortRankOne Q split hK μ n short hs hc) e h i a

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)

/-- In the original carrier the entire rank-one square uses Q.q itself. -/
theorem originalPinning_quotient (i : Fin 2)
    (hV : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (μ₀ : localGroup Q₀ split₀ i ≃* PSL(2,F)) (g : SL2 F) :
    let r := originalPinning Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ g
    Q₀.q ⟨r.val.val,parabolic_le_generated i r.val.property⟩ =
      sourcePinningHom Q₀ split₀ i hV μ₀ g := by
  dsimp only
  exact (original_endpointMap_apply Q₀ i
    (originalPinning Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ g)).symm.trans
      (originalPinning_endpoint Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ g)

variable (hm₀ : rotationOrder Q₀ = 6)
  (hK₀ : ∀ i, simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
  (μ₀ : ∀ i, localGroup Q₀ split₀ i ≃* PSL(2,F))
  (n₀ : ∀ i, RootReflection Q₀ split₀ i)
  (hs₀ : pinnedReflection Q₀ split₀ short (hK₀ short) (μ₀ short) = (n₀ short).val)
  (hc₀ : rankOne Q₀ split₀ short ≤ centralizer (positiveCarrier Q₀ split₀ short 0 : Set _))
  (d₀ : PartialPositiveData (sourceRoots Q₀ split₀ hK₀ μ₀ n₀ short))

/-- The positive map likewise retains the exact original quotient representative. -/
theorem sourceSylowHom_original_quotient (u : Atlas.G2.unipotent (K := F)) :
    let s := sourceSylowHom Q₀ split₀ (originalMarkedIso Q₀) hm₀ hK₀ μ₀ n₀ short hs₀ hc₀ d₀ h u
    Q₀.q ⟨s, (show S ≤ generated L S from le_sup_right) s.property⟩ =
      (sourceRoots Q₀ split₀ hK₀ μ₀ n₀ short).unipotentHom
        (source_positive_relations Q₀ split₀ hK₀ μ₀ n₀ short hs₀ hc₀ d₀).collection u :=
  CoordinatePositive.sourceSylowHom_original_quotient short h Q₀ split₀ hm₀ hK₀ μ₀ n₀ d₀
    (sourceShortRankOne Q₀ split₀ hK₀ μ₀ n₀ short hs₀ hc₀) u
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.PinningPositive
