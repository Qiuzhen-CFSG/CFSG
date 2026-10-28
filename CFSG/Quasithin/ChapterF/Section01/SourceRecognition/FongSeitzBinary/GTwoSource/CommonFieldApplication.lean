module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CommonFieldPinning
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GTwoSource.NonzeroPairingApplication

/-!
# Common-field source coordinates on the original marked Sylow

Choose the orientation supplied by the proved nonvanishing theorem and apply
the constructed whole-pinning field alignment. The normalized DC equation is
then a theorem on the actual marked quotient, for every finite characteristic-two
field. No pairing, coefficient, field-alignment or binary-field premise is added.

The existing G2Presentation.sourceSylowEquiv, obtained from the full original
overlap marking, pulls all six additive coordinates back to the original S.
DC holds in S itself, and both endpoint squares retain these same parameters.
For an original SourceQuotient the formulas use Q.q literally. The same
application accepts the supplied geometric amalgam marking.

This supplies the normalized mixed equation and its literal source application.
The new roots are normalizedSourceRoots, rather than the original independently
labeled alignedSourceRoots. Their complete Borel--Weyl relations and resulting
positive/full marked comparisons must still be connected to the existing
ShortModuleSource construction. Earlier local-model, radical-kernel, reflection
and whole-group generation premises remain source-assembly obligations.

Source: Fong--Seitz I (6E)(a), printed p.43; II (9.13)--(9.14), pp.215--216.
The constructor retains q=2, q=4 and both possible endpoint orientations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CommonFieldSource
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i)

/-- All field labels are constructed at the actual source orientation. -/
def roots : PositiveRoots F (X ⧸ Q.D) :=
  normalizedSourceRoots Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_middle_ne_bot Q split hK μ n hm)

/-- The exact normalized DC premise is proved on the constructed roots. -/
theorem dc (d c : F) :
    (roots Q split hm hK μ n).x 3 d*(roots Q split hm hK μ n).x 2 c =
      (roots Q split hm hK μ n).x 0 (c*d)*(roots Q split hm hK μ n).x 2 c*
        (roots Q split hm hK μ n).x 3 d :=
  normalizedSourceRoots_dc Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_middle_ne_bot Q split hK μ n hm) d c

theorem root_range (k : Fin 6) :
    ((roots Q split hm hK μ n).root k).range =
      positiveCarrier Q split (sourceOrientation Q split hK μ hm) k :=
  normalizedSourceRoots_range Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_middle_ne_bot Q split hK μ n hm) k

theorem roots_generated : (roots Q split hm hK μ n).generated=split.U :=
  normalizedSourceRoots_generated Q split hK μ n (sourceOrientation Q split hK μ hm) hm
    (sourceOrientation_middle_ne_bot Q split hK μ n hm)

/-- Each constructed root lies in the same original unipotent group. -/
def quotientRoot (k : Fin 6) : Multiplicative F →* split.U :=
  ((roots Q split hm hK μ n).root k).codRestrict split.U (fun a =>
    positiveCarrier_le Q split hm (sourceOrientation Q split hK μ hm) k
      (root_range Q split hm hK μ n k ▸ ⟨a,rfl⟩))

variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

/-- Pull the constructed coordinates through the existing full-overlap marking. -/
def sourceRoot (k : Fin 6) : Multiplicative F →* S :=
  (G2Presentation.sourceSylowEquiv Q split e h).symm.toMonoidHom.comp
    (quotientRoot Q split hm hK μ n k)

theorem sourceRoot_quotient (k : Fin 6) (a : F) :
    MarkedLocal.sylowMap Q e h (sourceRoot Q split hm hK μ n e h k (.ofAdd a)) =
      (roots Q split hm hK μ n).x k a := by
  exact congrArg Subtype.val ((G2Presentation.sourceSylowEquiv Q split e h).apply_symm_apply
    (quotientRoot Q split hm hK μ n k (.ofAdd a)))

/-- Both endpoint maps retain the exact same field parameters. -/
theorem sourceRoot_endpoint (i : Fin 2) (k : Fin 6) (a : F) :
    let s := sourceRoot Q split hm hK μ n e h k (.ofAdd a)
    MarkedLocal.endpointMap Q e i
      ⟨s,(show S ≤ parabolic L S i from le_sup_right.trans le_sup_left) s.property⟩ =
        (roots Q split hm hK μ n).x k a := by
  exact (MarkedLocal.endpoint_sylow Q e h i
    (sourceRoot Q split hm hK μ n e h k (.ofAdd a))).trans
      (sourceRoot_quotient Q split hm hK μ n e h k a)

/-- The normalized mixed equation holds in the original S, not only after
forgetting the original endpoint marking. -/
theorem sourceRoot_dc (d c : F) :
    sourceRoot Q split hm hK μ n e h 3 (.ofAdd d)*sourceRoot Q split hm hK μ n e h 2 (.ofAdd c) =
      sourceRoot Q split hm hK μ n e h 0 (.ofAdd (c*d))*
        sourceRoot Q split hm hK μ n e h 2 (.ofAdd c)*sourceRoot Q split hm hK μ n e h 3 (.ofAdd d) := by
  apply (Subtype.val_injective.comp (G2Presentation.sourceSylowEquiv Q split e h).injective)
  change MarkedLocal.sylowMap Q e h _=MarkedLocal.sylowMap Q e h _
  simp only [map_mul,sourceRoot_quotient]
  exact dc Q split hm hK μ n d c

section Original
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 6)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (h : HypothesisF11 L S)

/-- In the original carrier, every coordinate square uses literal Q.q. -/
theorem original_root_quotient (k : Fin 6) (a : F) :
    let s := sourceRoot Q split hm hK μ n (originalMarkedIso Q) h k (.ofAdd a)
    Q.q ⟨s,(show S ≤ generated L S from le_sup_right) s.property⟩ =
      (roots Q split hm hK μ n).x k a := by
  have he := sourceRoot_quotient Q split hm hK μ n (originalMarkedIso Q) h k a
  change ((originalMarkedIso Q).middle _ : (generated L S) ⧸ Q.D)=_ at he
  rwa [originalMarkedIso_middle_apply] at he
end Original
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.GTwoSource.CommonFieldSource
