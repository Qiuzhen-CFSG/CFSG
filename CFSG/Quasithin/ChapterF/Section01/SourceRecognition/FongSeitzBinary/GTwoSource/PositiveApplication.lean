module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.PositiveCoefficients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.G2Presentation.Positive

/-!
# The reconstructed coefficients on the literal marked source quotient

Apply the Fong–Seitz II (9.16)–(9.21) coefficient calculation to root maps
in `X / Q.D`, then use the published positive presentation and the original
amalgam marking. This discharges its EB equation and highest FE coefficient
from central containment, lower exchanges and the actual torus action.
Both original endpoint maps evaluate the same six-parameter word.

This application includes q = 4. The earlier root/module pinnings,
remaining intermediate equations, positive generation, and the separate
q = 2 branch are still obligations of source reconstruction. In particular
this is not (6E)(a) ⇒ (9A), and it does not supply the Weyl or rank-one words.
The earlier quotient and marking may be geometric; no map from the
universal completion to the generated source group is assumed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource
variable {G X K : Type*} [Group G] [Group X] [Field K] [CharP K 2] [Finite K]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (roots : PositiveRoots K (X ⧸ Q.D)) (d : PartialPositiveData roots)
  (hq : 4 ≤ Nat.card K) (hU : roots.generated = split.U)

include d hq in
/-- Complete the two unknown coefficients in this same source quotient. -/
theorem positiveRelations : roots.CharTwoRelations := by
  let := Fintype.ofFinite K
  exact d.relations (exists_nonprime_element (by simpa only [Nat.card_eq_fintype_card] using hq))

include d in
omit [CharP K 2] [Finite K] in
/-- The highest root is nontrivial at the unit parameter. -/
theorem highest_root_ne_one : roots.x 0 1 ≠ 1 := by
  intro he
  have hh := d.A_injective (he.trans (map_one (roots.root 0)).symm)
  have : (1 : K) = 0 := congrArg Multiplicative.toAdd hh
  exact one_ne_zero this

/-- The existing positive presentation maps onto the specified unipotent subgroup. -/
def quotientUnipotentHom : Atlas.G2.unipotent (K := K) →* split.U :=
  G2Presentation.quotientUnipotentHom Q split roots (positiveRelations Q roots d hq) hU

theorem quotientUnipotentHom_surjective :
    Function.Surjective (quotientUnipotentHom Q split roots d hq hU) :=
  G2Presentation.quotientUnipotentHom_surjective Q split roots (positiveRelations Q roots d hq) hU

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

/-- Pull back through the actual original common-Sylow marking. -/
def sourceSylowHom : Atlas.G2.unipotent (K := K) →* S :=
  G2Presentation.sourceSylowHom Q split roots (positiveRelations Q roots d hq) hU e h

theorem sourceSylowHom_surjective :
    Function.Surjective (sourceSylowHom Q split roots d hq hU e h) :=
  G2Presentation.sourceSylowHom_surjective Q split roots (positiveRelations Q roots d hq) hU e h

/-- Retain the literal quotient formula through the original marking. -/
theorem sourceSylowHom_quotient (u : Atlas.G2.unipotent (K := K)) :
    MarkedLocal.sylowMap Q e h (sourceSylowHom Q split roots d hq hU e h u) =
      roots.unipotentHom (positiveRelations Q roots d hq).collection u :=
  G2Presentation.sourceSylowHom_quotient Q split roots (positiveRelations Q roots d hq) hU e h u

/-- Both original endpoint embeddings agree on every collected positive word. -/
theorem sourceSylowHom_endpoint (i : Fin 2) (t : Fin 6 → K) :
    let s := sourceSylowHom Q split roots d hq hU e h (Atlas.G2.unipotentEquiv t)
    MarkedLocal.endpointMap Q e i
      ⟨s, (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        roots.product t :=
  G2Presentation.sourceSylowHom_endpoint Q split roots (positiveRelations Q roots d hq) hU e h i t

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource
