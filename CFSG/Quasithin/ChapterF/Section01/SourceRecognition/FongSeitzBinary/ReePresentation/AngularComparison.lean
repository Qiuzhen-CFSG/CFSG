module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceAngular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.Positive

/-!
# Full unipotent comparison on the original and geometric Ree markings

The proved angular presentation has faithful native and source evaluations.
Composing the source comparison with the actual original Sylow marking gives
an isomorphism from the same original S to the full native U, including m = 0.
Both endpoint inclusion squares and the common-Borel square restricted to S
use this one isomorphism. The quotient-overlap lift uses the literal Q.q.
The supplied amalgam marking may be original or universal/geometric.

Charts and finite source equations remain with the recognition owner. This
positive comparison does not yet identify the full Borel or either parabolic.
Source: DGS, *Groups and Graphs*, p.224; Aschbacher--Smith F.1.1--3,
pp.259--261; GLS3 2.3.7 and 2.4.5--6.
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

/-- The actual original common Sylow is isomorphic to the entire native U.
This applies with either the original or universal/geometric marked quotient. -/
def originalUnipotentEquiv : S ≃* ReeF4.Parabolics.unipotent m :=
  (sourceSylowEquiv Q e h split).trans (SourceAngular.comparison Q split d E)

/-- The inverse comparison keeps exactly the original Sylow marking. -/
theorem originalUnipotentEquiv_symm_apply (u : ReeF4.Parabolics.unipotent m) :
    MarkedLocal.sylowMap Q e h ((originalUnipotentEquiv Q e h split d E).symm u) =
      ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D) := by
  change (sourceSylowEquiv Q e h split
    ((sourceSylowEquiv Q e h split).symm ((SourceAngular.comparison Q split d E).symm u))
    : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]

/-- Both literal endpoint inclusion squares agree on this full Sylow comparison. -/
theorem originalUnipotentEquiv_endpoint (u : ReeF4.Parabolics.unipotent m) (i : Fin 2) :
    MarkedLocal.endpointMap Q e i
      ⟨(originalUnipotentEquiv Q e h split d E).symm u,
        (show S ≤ parabolic L S i from le_sup_right.trans le_sup_left)
          ((originalUnipotentEquiv Q e h split d E).symm u).property⟩ =
      ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D) := by
  rw [MarkedLocal.endpoint_sylow Q e h, originalUnipotentEquiv_symm_apply]

/-- The common-Borel square restricted to S uses the same isomorphism. -/
theorem originalUnipotentEquiv_borel (u : ReeF4.Parabolics.unipotent m) :
    MarkedLocal.borelMap Q e h
      ⟨(originalUnipotentEquiv Q e h split d E).symm u,
        (show S ≤ commonBorel L S from le_sup_right)
          ((originalUnipotentEquiv Q e h split d E).symm u).property⟩ =
      ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D) :=
  originalUnipotentEquiv_symm_apply Q e h split d E u

/-- Every field generator is carried by the literal original lift. -/
theorem originalUnipotentEquiv_field (i : PositiveTables.Root)
    (a : PositiveTables.Parameter m i) (s : S)
    (hs : MarkedLocal.sylowMap Q e h s = (d.chart i a : X ⧸ Q.D)) :
    (originalUnipotentEquiv Q e h split d E s : ReeF4.Model m) = PositiveTables.root m i a := by
  have he : sourceSylowEquiv Q e h split s =
      ⟨d.chart i a, SourcePositive.root_le_unipotent Q split d i (d.chart i a).property⟩ :=
    Subtype.ext hs
  change (SourceAngular.comparison Q split d E (sourceSylowEquiv Q e h split s) : ReeF4.Model m) = _
  rw [he]
  exact SourceAngular.comparison_field Q split d E i a

/-- The marked quotient's literal common-overlap lift of every native positive element. -/
def quotientUnipotentLift : ReeF4.Parabolics.unipotent m →* (P 0 ⊓ P 1 : Subgroup X) :=
  Q.borelEquiv.symm.toMonoidHom.comp
    ((Subgroup.inclusion split.U_le).comp (SourceAngular.comparison Q split d E).symm.toMonoidHom)

theorem quotientUnipotentLift_square (u : ReeF4.Parabolics.unipotent m) :
    Q.q (quotientUnipotentLift Q split d E u) =
      ((SourceAngular.comparison Q split d E).symm u : X ⧸ Q.D) := by
  change Q.q (Q.borelEquiv.symm _) = _
  rw [← Q.borelEquiv_apply, MulEquiv.apply_symm_apply]
  rfl

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
