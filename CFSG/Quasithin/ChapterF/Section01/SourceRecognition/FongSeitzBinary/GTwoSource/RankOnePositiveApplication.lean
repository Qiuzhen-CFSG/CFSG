module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.WeylCoefficient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.PositiveApplication

/-!
# Positive G₂ reconstruction using the actual short rank-one pinning

On the same marked quotient, the short SL₂ cubic determines the highest
FE coefficient even over F₂. Apply the published positive presentation
with these proved coefficients and transport through the original common
Sylow marking. Both endpoint formulas use the same six-parameter word.
For a SourceQuotient the final formula is the literal original quotient map.

The module requires intermediate lower root equations, torus actions,
positive generation and a short rank-one pinning. Constructing these from
Fong–Seitz I (6E)(a), including the binary branch, remains source work.
No complete Borel–Weyl relations or model recognition are assumed here.
Source: Fong–Seitz II §9A, (9.13)–(9.21), printed pp.215–217, with the
rank-one cubic replacing the q ≥ 4 scalar normalization in (9.21).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.RankOnePositive
variable {G X K : Type*} [Group G] [Group X] [Field K] [CharP K 2] [Finite K]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (roots : PositiveRoots K (X ⧸ Q.D)) (d : PartialPositiveData roots)
  (p : ShortRankOneData roots) (hU : roots.generated = split.U)

include d p in
/-- All fifteen positive relations, with no exclusion of q=2 or q=4. -/
theorem positiveRelations : roots.CharTwoRelations := d.relations_of_short_rankOne p

/-- The literal model positive subgroup maps onto the specified source U. -/
def quotientUnipotentHom : Atlas.G2.unipotent (K := K) →* split.U :=
  G2Presentation.quotientUnipotentHom Q split roots (positiveRelations Q roots d p) hU

theorem quotientUnipotentHom_surjective :
    Function.Surjective (quotientUnipotentHom Q split roots d p hU) :=
  G2Presentation.quotientUnipotentHom_surjective Q split roots (positiveRelations Q roots d p) hU

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

/-- The same positive presentation maps onto the original S. -/
def sourceSylowHom : Atlas.G2.unipotent (K := K) →* S :=
  G2Presentation.sourceSylowHom Q split roots (positiveRelations Q roots d p) hU e h

theorem sourceSylowHom_surjective :
    Function.Surjective (sourceSylowHom Q split roots d p hU e h) :=
  G2Presentation.sourceSylowHom_surjective Q split roots (positiveRelations Q roots d p) hU e h

/-- The original overlap and quotient marking are retained. -/
theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := K)) :
    MarkedLocal.sylowMap Q e h (sourceSylowHom Q split roots d p hU e h u) =
      roots.unipotentHom (positiveRelations Q roots d p).collection u :=
  G2Presentation.sourceSylowHom_quotient Q split roots (positiveRelations Q roots d p) hU e h u

/-- Both literal endpoint representatives evaluate the same positive word. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (t : Fin 6 → K) :
    let s := sourceSylowHom Q split roots d p hU e h (Atlas.G2.unipotentEquiv t)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        roots.product t :=
  G2Presentation.sourceSylowHom_endpoint Q split roots (positiveRelations Q roots d p) hU e h i t

section Original
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  (roots₀ : PositiveRoots K ((generated L S) ⧸ Q₀.D))
  (d₀ : PartialPositiveData roots₀) (p₀ : ShortRankOneData roots₀)
  (hU₀ : roots₀.generated = split₀.U)

/-- In the original generated source carrier, the formula uses Q.q itself. -/
theorem sourceSylowHom_original_quotient (u : Atlas.G2.unipotent (K := K)) :
    let s := sourceSylowHom Q₀ split₀ roots₀ d₀ p₀ hU₀ (originalMarkedIso Q₀) h u
    Q₀.q ⟨s, (show S ≤ generated L S from le_sup_right) s.property⟩ =
      roots₀.unipotentHom (positiveRelations Q₀ roots₀ d₀ p₀).collection u := by
  have he := sourceSylowHom_quotient Q₀ split₀ roots₀ d₀ p₀ hU₀ (originalMarkedIso Q₀) h u
  change ((originalMarkedIso Q₀).middle _ : (generated L S) ⧸ Q₀.D) = _ at he
  rwa [originalMarkedIso_middle_apply] at he
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.RankOnePositive
