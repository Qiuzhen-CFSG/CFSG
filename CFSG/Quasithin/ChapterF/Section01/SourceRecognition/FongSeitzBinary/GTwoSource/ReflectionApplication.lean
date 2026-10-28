module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.AlignedPositive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.RankOnePositiveApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootLocalCover

/-!
# Reflection-aligned G₂ source maps on the original marked quotient

Both whole SL₂ pinnings now send the Weyl matrix to the specified source
reflection in Rᵢ ∩ N. Pull them back through the literal endpoint equivalences;
these squares hold on every SL₂ element. Their six positive root maps generate
the original U and have nontrivial highest root. The published positive
presentation then maps onto the original S with both endpoint formulas intact.
The same statements accept the original or geometric amalgam isomorphism;
for a SourceQuotient the square uses the original Q.q.

The remaining explicit premises are the orthogonal-root centralizer and
PartialPositiveData. Their derivation from (6E)(a), the coupled natural/tensor
modules, the reverse Cartan containment and full Borel--Weyl relations are
still source obligations. No Weyl-alignment certificate is assumed here,
and neither q=2 nor q=4 is excluded.

Source: Fong--Seitz II §7, printed p.192, and (9.6), (9.9)--(9.21),
printed pp.212--217. Earlier local-section/kernel premises retain their
existing source producers and their discharge by final source assembly.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.ReflectionPositive
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

/-- The whole aligned map is pulled back through the actual endpoint equivalence. -/
def originalPinning (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) :
    SL2 F ≃* MarkedLocal.originalRankOne Q e split i :=
  (alignedPinning Q split i hV μ n).trans (MarkedLocal.originalRankOneEquiv Q e split i).symm

theorem originalPinning_endpoint (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) (g : SL2 F) :
    MarkedLocal.endpointMap Q e i (originalPinning Q split e i hV μ n g) =
      alignedPinningHom Q split i hV μ n g := by
  rw [← MarkedLocal.originalRankOneEquiv_apply]
  change ((MarkedLocal.originalRankOneEquiv Q e split i)
    ((MarkedLocal.originalRankOneEquiv Q e split i).symm
      (alignedPinning Q split i hV μ n g)) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply,alignedPinning_coe]

/-- At either endpoint, the Weyl matrix gives the specified source lift. -/
theorem originalPinning_reflection (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (n : RootReflection Q split i) :
    MarkedLocal.endpointMap Q e i (originalPinning Q split e i hV μ n (weyl F)) = n.val := by
  rw [originalPinning_endpoint,alignedPinningHom_weyl]

variable (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

include hm in
/-- Positive generation, nontriviality and both literal endpoint placements. -/
theorem coordinates :
    (alignedSourceRoots Q split hK μ n short).generated = split.U ∧
    (alignedSourceRoots Q split hK μ n short).x 0 1 ≠ 1 ∧
    ((n short).val : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple short} ∧
    ((n (1-short)).val : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple (1-short)} :=
  ⟨alignedSourceRoots_generated Q split hK μ n short hm,
    alignedSourceRoots_highest_nontrivial Q split hK μ n short,
    sourceReflection_placements Q split n short⟩

variable
  (hc : rankOne Q split short ≤ centralizer (positiveCarrier Q split short 0 : Set (X ⧸ Q.D)))
  (d : PartialPositiveData (alignedSourceRoots Q split hK μ n short))
  (h : HypothesisF11 L S)

/-- Apply the published positive presentation to these actual quotient maps. -/
def quotientUnipotentHom : Atlas.G2.unipotent (K := F) →* split.U :=
  RankOnePositive.quotientUnipotentHom Q split (alignedSourceRoots Q split hK μ n short) d
    (alignedShortRankOne Q split hK μ n short hc)
    (alignedSourceRoots_generated Q split hK μ n short hm)

theorem quotientUnipotentHom_surjective :
    Function.Surjective (quotientUnipotentHom Q split hm hK μ n short hc d) :=
  RankOnePositive.quotientUnipotentHom_surjective Q split (alignedSourceRoots Q split hK μ n short) d
    (alignedShortRankOne Q split hK μ n short hc)
    (alignedSourceRoots_generated Q split hK μ n short hm)

/-- Retain the original common Sylow through the supplied amalgam marking. -/
def sourceSylowHom : Atlas.G2.unipotent (K := F) →* S :=
  RankOnePositive.sourceSylowHom Q split (alignedSourceRoots Q split hK μ n short) d
    (alignedShortRankOne Q split hK μ n short hc)
    (alignedSourceRoots_generated Q split hK μ n short hm) e h

theorem sourceSylowHom_surjective :
    Function.Surjective (sourceSylowHom Q split e hm hK μ n short hc d h) :=
  RankOnePositive.sourceSylowHom_surjective Q split (alignedSourceRoots Q split hK μ n short) d
    (alignedShortRankOne Q split hK μ n short hc)
    (alignedSourceRoots_generated Q split hK μ n short hm) e h

theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := F)) :
    MarkedLocal.sylowMap Q e h (sourceSylowHom Q split e hm hK μ n short hc d h u) =
      (alignedSourceRoots Q split hK μ n short).unipotentHom
        (aligned_positive_relations Q split hK μ n short hc d).collection u :=
  RankOnePositive.sourceSylowHom_quotient Q split (alignedSourceRoots Q split hK μ n short) d
    (alignedShortRankOne Q split hK μ n short hc)
    (alignedSourceRoots_generated Q split hK μ n short hm) e h u

/-- The same six-parameter source word occurs at both original endpoints. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (a : Fin 6 → F) :
    let s := sourceSylowHom Q split e hm hK μ n short hc d h (Atlas.G2.unipotentEquiv a)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        (alignedSourceRoots Q split hK μ n short).product a :=
  RankOnePositive.sourceSylowHom_endpoint Q split (alignedSourceRoots Q split hK μ n short) d
    (alignedShortRankOne Q split hK μ n short hc)
    (alignedSourceRoots_generated Q split hK μ n short hm) e h i a

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)

theorem originalPinning_quotient (i : Fin 2)
    (hV : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (μ₀ : localGroup Q₀ split₀ i ≃* PSL(2,F)) (n₀ : RootReflection Q₀ split₀ i) (g : SL2 F) :
    let r := originalPinning Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ n₀ g
    Q₀.q ⟨r.val.val,parabolic_le_generated i r.val.property⟩ =
      alignedPinningHom Q₀ split₀ i hV μ₀ n₀ g := by
  dsimp only
  exact (original_endpointMap_apply Q₀ i
    (originalPinning Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ n₀ g)).symm.trans
      (originalPinning_endpoint Q₀ split₀ (originalMarkedIso Q₀) i hV μ₀ n₀ g)

variable (hm₀ : rotationOrder Q₀ = 6)
  (hK₀ : ∀ i, simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
  (μ₀ : ∀ i, localGroup Q₀ split₀ i ≃* PSL(2,F))
  (n₀ : ∀ i, RootReflection Q₀ split₀ i)
  (hc₀ : rankOne Q₀ split₀ short ≤ centralizer (positiveCarrier Q₀ split₀ short 0 : Set _))
  (d₀ : PartialPositiveData (alignedSourceRoots Q₀ split₀ hK₀ μ₀ n₀ short))

/-- The positive application likewise uses the original quotient map itself. -/
theorem sourceSylowHom_original_quotient (u : Atlas.G2.unipotent (K := F)) :
    let s := sourceSylowHom Q₀ split₀ (originalMarkedIso Q₀) hm₀ hK₀ μ₀ n₀ short hc₀ d₀ h u
    Q₀.q ⟨s, (show S ≤ generated L S from le_sup_right) s.property⟩ =
      (alignedSourceRoots Q₀ split₀ hK₀ μ₀ n₀ short).unipotentHom
        (aligned_positive_relations Q₀ split₀ hK₀ μ₀ n₀ short hc₀ d₀).collection u :=
  RankOnePositive.sourceSylowHom_original_quotient h Q₀ split₀
    (alignedSourceRoots Q₀ split₀ hK₀ μ₀ n₀ short) d₀
    (alignedShortRankOne Q₀ split₀ hK₀ μ₀ n₀ short hc₀)
    (alignedSourceRoots_generated Q₀ split₀ hK₀ μ₀ n₀ short hm₀) u
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.ReflectionPositive
