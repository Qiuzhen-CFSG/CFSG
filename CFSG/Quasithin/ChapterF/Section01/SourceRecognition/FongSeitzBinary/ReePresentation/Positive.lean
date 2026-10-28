module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourcePositive
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.RankOne

/-!
# Positive Ree relators on original and geometric source markings

The finite source root equations construct evaluation into the original U.
Its entire range is obtained from Carter's coordinates on the same quotient.
The original common Sylow is carried to U by the supplied whole-overlap
marking, so every abstract positive word has a unique original Sylow lift.
Both endpoint squares and the common-Borel square use that single lift.
The numerator may be the generated group or the universal completion.
No model comparison or positive-presentation faithfulness is asserted here.

Source: DGS, Groups and Graphs, Theorem D, p.224; Aschbacher–Smith F.1.1–3,
pp.259–260; GLS3 2.3.7 and 2.4.5.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {m : ℕ} (d : SourcePositive.Charts Q split m)

/-- The original whole-overlap marking is injective on its common Sylow. -/
theorem sourceSylowMap_injective : Function.Injective (MarkedLocal.sylowMap Q e h) := by
  intro a b hab
  let eb : commonBorel L S ≃* Q.tits.B :=
    (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
  have he : eb ⟨a, (show S ≤ commonBorel L S from le_sup_right) a.property⟩ =
      eb ⟨b, (show S ≤ commonBorel L S from le_sup_right) b.property⟩ := Subtype.ext hab
  apply Subtype.ext
  exact congrArg (fun z : commonBorel L S => (z : G)) (eb.injective he)

/-- The original common Sylow, with its literal marking, is the source U. -/
def sourceSylowEquiv : S ≃* split.U :=
  (MonoidHom.ofInjective (sourceSylowMap_injective Q e h)).trans
    (MulEquiv.subgroupCongr (MarkedLocal.sylow_range Q e h split))

@[simp] theorem sourceSylowEquiv_apply (s : S) :
    (sourceSylowEquiv Q e h split s : X ⧸ Q.D) = MarkedLocal.sylowMap Q e h s := rfl

/-- The source equations construct the original positive-word evaluation as a
homomorphism into S; it is not supplied as a premise. -/
def originalPositiveEval : PositivePresentation.Presentation m →* S :=
  (sourceSylowEquiv Q e h split).symm.toMonoidHom.comp
    ((SourcePositive.eval Q split d).codRestrict split.U
      (fun g => SourcePositive.eval_range_le Q split d ⟨g,rfl⟩))

/-- The constructed original evaluation retains the same source quotient map. -/
theorem originalPositiveEval_apply (g : PositivePresentation.Presentation m) :
    MarkedLocal.sylowMap Q e h (originalPositiveEval Q e h split d g) =
      SourcePositive.eval Q split d g := by
  change (sourceSylowEquiv Q e h split ((sourceSylowEquiv Q e h split).symm _)
    : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- No elements of the original common Sylow are omitted. -/
theorem originalPositiveEval_surjective :
    Function.Surjective (originalPositiveEval Q e h split d) := by
  intro s
  have hs : MarkedLocal.sylowMap Q e h s ∈ (SourcePositive.eval Q split d).range := by
    rw [SourcePositive.eval_range, ← MarkedLocal.sylow_range Q e h split]
    exact ⟨s,rfl⟩
  obtain ⟨g,hg⟩ := hs
  refine ⟨g, ?_⟩
  apply sourceSylowMap_injective Q e h
  rw [originalPositiveEval_apply, hg]

/-- The original endpoint square holds in either orientation for the same lift. -/
theorem originalPositiveEval_endpoint (g : PositivePresentation.Presentation m) (i : Fin 2) :
    MarkedLocal.endpointMap Q e i
      ⟨originalPositiveEval Q e h split d g,
        (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left)
          (originalPositiveEval Q e h split d g).property⟩ = SourcePositive.eval Q split d g := by
  rw [MarkedLocal.endpoint_sylow Q e h, originalPositiveEval_apply]

/-- The full-overlap marking agrees on every constructed positive word. -/
theorem originalPositiveEval_borel (g : PositivePresentation.Presentation m) :
    MarkedLocal.borelMap Q e h
      ⟨originalPositiveEval Q e h split d g,
        (show S ≤ commonBorel L S from le_sup_right)
          (originalPositiveEval Q e h split d g).property⟩ = SourcePositive.eval Q split d g :=
  originalPositiveEval_apply Q e h split d g

/-- Original source equality is determined by that one marked evaluation. -/
theorem originalPositiveEval_unique (g : PositivePresentation.Presentation m) (s : S)
    (hs : MarkedLocal.sylowMap Q e h s = SourcePositive.eval Q split d g) :
    s = originalPositiveEval Q e h split d g := by
  apply sourceSylowMap_injective Q e h
  rw [originalPositiveEval_apply, hs]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
