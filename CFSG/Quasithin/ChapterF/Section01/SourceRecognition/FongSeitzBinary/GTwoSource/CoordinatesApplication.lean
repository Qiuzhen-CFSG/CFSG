module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PositiveCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.RankOnePositiveApplication

/-!
# Constructed source root coordinates in the literal positive consumer

The canonical panel maps give additive field coordinates on each source
simple root, including at q=2. Transport along the same source reflections
constructs all six root maps. Their generated subgroup is the specified U,
the highest root is nontrivial, and both source reflection placements are
retained for either orientation.

Apply the existing positive presentation with these actual maps and the
proved generation equality, then pull it back through the supplied original
or geometric amalgam marking. The original S and both endpoint representative
formulas remain literal; on a SourceQuotient the square uses Q.q itself.

The lower equations in PartialPositiveData and the compatible short SL₂
pinning in ShortRankOneData remain explicit intermediate premises. This
module removes the additive-coordinate, positive-generation and nontriviality
obligations; it does not construct the coupled rank-one modules, align their
field labelings, or claim the full Borel--Weyl relations. Those are still
needed to derive the complete source theorem from I (6E)(a), including q=2.

Source: Fong--Seitz I (5C), (6E)(a), printed pp.25--28 and43;
II (9.9)--(9.21), printed pp.213--217.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CoordinatePositive
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

include hm in
/-- The literal source A--F roots, with their required positive subgroup and
nontrivial highest root and both endpoint placements, follow from the actual
local PSL₂ comparisons and the specified source reflections. -/
theorem coordinates :
    (sourceRoots Q split hK μ n short).generated = split.U ∧
    (sourceRoots Q split hK μ n short).x 0 1 ≠ 1 ∧
    ((n short).val : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple short} ∧
    ((n (1-short)).val : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple (1-short)} :=
  ⟨sourceRoots_generated Q split hK μ n short hm,
    sourceRoots_highest_nontrivial Q split hK μ n short,
    sourceReflection_placements Q split n short⟩

variable (d : PartialPositiveData (sourceRoots Q split hK μ n short)) (p : ShortRankOneData (sourceRoots Q split hK μ n short))

/-- No positive-generation hypothesis remains in this application. -/
def quotientUnipotentHom : Atlas.G2.unipotent (K := F) →* split.U :=
  RankOnePositive.quotientUnipotentHom Q split (sourceRoots Q split hK μ n short) d p
    (sourceRoots_generated Q split hK μ n short hm)

theorem quotientUnipotentHom_surjective :
    Function.Surjective (quotientUnipotentHom Q split hm hK μ n short d p) :=
  RankOnePositive.quotientUnipotentHom_surjective Q split (sourceRoots Q split hK μ n short) d p
    (sourceRoots_generated Q split hK μ n short hm)

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

/-- Pull back through the supplied original or geometric marking, retaining S. -/
def sourceSylowHom : Atlas.G2.unipotent (K := F) →* S :=
  RankOnePositive.sourceSylowHom Q split (sourceRoots Q split hK μ n short) d p
    (sourceRoots_generated Q split hK μ n short hm) e h

theorem sourceSylowHom_surjective :
    Function.Surjective (sourceSylowHom Q split hm hK μ n short d p e h) :=
  RankOnePositive.sourceSylowHom_surjective Q split (sourceRoots Q split hK μ n short) d p
    (sourceRoots_generated Q split hK μ n short hm) e h

/-- The original common-Sylow map uses these very same quotient root maps. -/
theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := F)) :
    MarkedLocal.sylowMap Q e h (sourceSylowHom Q split hm hK μ n short d p e h u) =
      (sourceRoots Q split hK μ n short).unipotentHom (d.relations_of_short_rankOne p).collection u :=
  RankOnePositive.sourceSylowHom_quotient Q split (sourceRoots Q split hK μ n short) d p
    (sourceRoots_generated Q split hK μ n short hm) e h u

/-- Both actual endpoint maps evaluate the same six source root coordinates. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (a : Fin 6 → F) :
    let s := sourceSylowHom Q split hm hK μ n short d p e h (Atlas.G2.unipotentEquiv a)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        (sourceRoots Q split hK μ n short).product a :=
  RankOnePositive.sourceSylowHom_endpoint Q split (sourceRoots Q split hK μ n short) d p
    (sourceRoots_generated Q split hK μ n short hm) e h i a

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  (hm₀ : rotationOrder Q₀ = 6)
  (hK₀ : ∀ i, simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
  (μ₀ : ∀ i, localGroup Q₀ split₀ i ≃* PSL(2,F))
  (n₀ : ∀ i, RootReflection Q₀ split₀ i)
  (d₀ : PartialPositiveData (sourceRoots Q₀ split₀ hK₀ μ₀ n₀ short))
  (p₀ : ShortRankOneData (sourceRoots Q₀ split₀ hK₀ μ₀ n₀ short))

/-- In the original carrier the square uses the original quotient map Q.q. -/
theorem sourceSylowHom_original_quotient (u : Atlas.G2.unipotent (K := F)) :
    let s := sourceSylowHom Q₀ split₀ hm₀ hK₀ μ₀ n₀ short d₀ p₀ (originalMarkedIso Q₀) h u
    Q₀.q ⟨s, (show S ≤ generated L S from le_sup_right) s.property⟩ =
      (sourceRoots Q₀ split₀ hK₀ μ₀ n₀ short).unipotentHom
        (d₀.relations_of_short_rankOne p₀).collection u :=
  RankOnePositive.sourceSylowHom_original_quotient h Q₀ split₀
    (sourceRoots Q₀ split₀ hK₀ μ₀ n₀ short) d₀ p₀
    (sourceRoots_generated Q₀ split₀ hK₀ μ₀ n₀ short hm₀) u
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CoordinatePositive
