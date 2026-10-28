module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.AngularComparison

/-!
# Full original and geometric common-Borel comparison for the Ree row

The finite positive and full-Cartan equations give an actual isomorphism of
the original common Borel with the entire native Borel. Its restriction to S
is the already constructed full unipotent isomorphism. The common-overlap and
both endpoint inclusion squares commute at every Borel element; the literal
quotient version uses Q.q throughout. The numerator may be the original group
or the universal/geometric completion.

This does not yet extend to either whole parabolic or the full Ree group.
Source equations remain with the split-recognition owner.
Source: DGS, *Groups and Graphs*, p.224; Aschbacher--Smith F.1.1--3,
pp.259--261; GLS3 2.3.4--8 and 2.4.5--6.
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
  {m : ℕ} (d : SourcePositive.Charts Q split m) (E : SourceAngular.Equations Q split d)
  (T : SourceBorel.TorusData Q split d)

/-- The entire original common Borel, with the original whole-overlap marking. -/
def originalBorelEquiv : commonBorel L S ≃* ReeF4.Parabolics.borel m :=
  ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle).trans
    (SourceBorel.comparison Q split d E T).symm

/-- The full common-Borel square uses the original marking at every element. -/
theorem originalBorelEquiv_square (b : commonBorel L S) :
    (SourceBorel.comparison Q split d E T (originalBorelEquiv Q e h split d E T b) : X ⧸ Q.D) =
      MarkedLocal.borelMap Q e h b := by
  change (SourceBorel.comparison Q split d E T
    ((SourceBorel.comparison Q split d E T).symm _) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Either endpoint square commutes on the whole common Borel. -/
theorem originalBorelEquiv_endpoint (b : commonBorel L S) (i : Fin 2) :
    MarkedLocal.endpointMap Q e i ⟨b, commonBorel_le_parabolic i b.property⟩ =
      (SourceBorel.comparison Q split d E T (originalBorelEquiv Q e h split d E T b) : X ⧸ Q.D) := by
  rw [MarkedLocal.endpoint_borel Q e h, originalBorelEquiv_square]

/-- Restriction to S is exactly the previously constructed positive comparison. -/
theorem originalBorelEquiv_sylow (s : S) :
    (originalBorelEquiv Q e h split d E T
      ⟨s, (show S ≤ commonBorel L S from le_sup_right) s.property⟩ : ReeF4.Model m) =
      originalUnipotentEquiv Q e h split d E s := by
  let u := originalUnipotentEquiv Q e h split d E s
  have he : originalBorelEquiv Q e h split d E T
      ⟨s, (show S ≤ commonBorel L S from le_sup_right) s.property⟩ =
      ⟨u, ReeF4.Parabolics.unipotent_le_borel m u.property⟩ := by
    apply (SourceBorel.comparison Q split d E T).injective
    apply Subtype.ext
    rw [originalBorelEquiv_square, SourceBorel.comparison_unipotent]
    change (sourceSylowEquiv Q e h split s : X ⧸ Q.D) =
      ((SourceAngular.comparison Q split d E).symm
        (SourceAngular.comparison Q split d E (sourceSylowEquiv Q e h split s)) : X ⧸ Q.D)
    rw [MulEquiv.symm_apply_apply]
  exact congrArg Subtype.val he

/-- The literal quotient lift carries all of the native Borel, including its
entire Cartan. No replacement quotient map is introduced. -/
def quotientBorelEquiv : (P 0 ⊓ P 1 : Subgroup X) ≃* ReeF4.Parabolics.borel m :=
  Q.borelEquiv.trans (SourceBorel.comparison Q split d E T).symm

theorem quotientBorelEquiv_square (b : (P 0 ⊓ P 1 : Subgroup X)) :
    (SourceBorel.comparison Q split d E T (quotientBorelEquiv Q split d E T b) : X ⧸ Q.D) = Q.q b := by
  change (SourceBorel.comparison Q split d E T
    ((SourceBorel.comparison Q split d E T).symm (Q.borelEquiv b)) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply, Q.borelEquiv_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
