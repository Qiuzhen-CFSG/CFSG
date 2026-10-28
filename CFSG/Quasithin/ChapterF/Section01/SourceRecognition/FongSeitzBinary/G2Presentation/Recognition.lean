module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Markings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.G2Presentation.Positive
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.G2

/-!
# Full marked G₂ recognition on the original DGS quotient

The proved presentation constructs one ambient equivalence preserving every
root, the full torus and both reflections. Normalizers identify the whole
Borel; the short and long reflection placements identify both original
parabolics. Restriction and composition with the supplied original/geometric
marking preserve both inclusion squares on the whole overlap.

The numerator may be an infinite universal completion. No descent to the
original generated ambient group is assumed. The source recognition owner
still supplies the compatible field, explicit equations, generation and
placements. This conditional application discharges presentation-to-model
recognition, not the exhaustive DGS alternatives or their earlier premises.
Source: DGS, Groups and Graphs, Theorem D, p.224; Aschbacher–Smith F.1.11–12.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Atlas.G2.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.G2Presentation
variable {G X F : Type*} [Group G] [Group X] [Field F]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

variable (split : SplitData Q.tits)

variable [Finite F] [CharP F 2] {shortIndex : Fin 2}
  (d : RootData Q split F shortIndex)

/-- The actual quotient equivalence, preserving all six roots and parameters. -/
def quotientEquiv : (X ⧸ Q.D) ≃* Atlas.G2.Model F :=
  Atlas.G2.RootPresentationRecognition.quotientEquiv Q split d

@[simp] theorem quotientEquiv_root (i : Fin 6) (a : F) :
    quotientEquiv Q split d (d.data.x i a) = (modelData (F := F)).x i a :=
  Atlas.G2.RootPresentationRecognition.quotientEquiv_root Q split d i a

@[simp] theorem quotientEquiv_torus (p : Fˣ × Fˣ) :
    quotientEquiv Q split d (d.data.torus p) = Atlas.G2.torusHom p :=
  Atlas.G2.RootPresentationRecognition.quotientEquiv_torus Q split d p

@[simp] theorem quotientEquiv_r : quotientEquiv Q split d d.data.r = Atlas.G2.weylR :=
  Atlas.G2.RootPresentationRecognition.quotientEquiv_r Q split d

@[simp] theorem quotientEquiv_s : quotientEquiv Q split d d.data.s = Atlas.G2.weylS :=
  Atlas.G2.RootPresentationRecognition.quotientEquiv_s Q split d

/-- The actual source U, full Borel, and both marked vertices, including reverse
orientation, are compared by this one root-preserving equivalence. -/
theorem subgroup_images :
    split.U.map (quotientEquiv Q split d).toMonoidHom = Atlas.G2.unipotent ∧
    Q.tits.B.map (quotientEquiv Q split d).toMonoidHom = Atlas.G2.borel ∧
    (Q.tits.standardParabolic {Q.simple shortIndex}).map
      (quotientEquiv Q split d).toMonoidHom = Atlas.G2.LieParabolicSetup.parabolic₁ ∧
    (Q.tits.standardParabolic {Q.simple (1 - shortIndex)}).map
      (quotientEquiv Q split d).toMonoidHom = Atlas.G2.LieParabolicSetup.parabolic₂ :=
  ⟨Atlas.G2.RootPresentationRecognition.quotientEquiv_unipotent Q split d, Atlas.G2.RootPresentationRecognition.quotientEquiv_borel Q split d,
    Atlas.G2.RootPresentationRecognition.quotientEquiv_short Q split d, Atlas.G2.RootPresentationRecognition.quotientEquiv_long Q split d⟩

/-- Restrict the constructed ambient equivalence and compose with the literal
original/geometric source marking, retaining both inclusion squares. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F shortIndex) :=
  e.trans (markedIso Q split d)

@[simp] theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison Q e split d).left a : Atlas.G2.Model F) =
      quotientEquiv Q split d ((e.left a : Q.tits.standardParabolic {Q.simple 0}) :
        X ⧸ Q.D) := rfl

/-- The formula holds on the entire overlap, rather than only its Sylow. -/
@[simp] theorem comparison_middle_apply
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e split d).middle b : Atlas.G2.Model F) =
      quotientEquiv Q split d (e.middle b : X ⧸ Q.D) := rfl

@[simp] theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison Q e split d).right a : Atlas.G2.Model F) =
      quotientEquiv Q split d ((e.right a : Q.tits.standardParabolic {Q.simple 1}) :
        X ⧸ Q.D) := rfl

/-- Literal left endpoint square for the original inclusion amalgam. -/
theorem comparison_left_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e split d).left ⟨b, b.property.1⟩ =
      (flagAmalgam F shortIndex).left ((comparison Q e split d).middle b) :=
  (comparison Q e split d).left_commutes b

/-- Literal right endpoint square for that same whole original overlap. -/
theorem comparison_right_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e split d).right ⟨b, b.property.2⟩ =
      (flagAmalgam F shortIndex).right ((comparison Q e split d).middle b) :=
  (comparison Q e split d).right_commutes b

/-- The common Borel formula uses exactly MarkedLocal's full-overlap map. -/
theorem comparison_commonBorel_apply (b : commonBorel L S) :
    ((comparison Q e split d).middle
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) : Atlas.G2.Model F) =
      quotientEquiv Q split d (MarkedLocal.borelMap Q e h b) := rfl

/-- The original Sylow has exactly the model unipotent image, under the
same common-Borel/quotient map used on every original endpoint. -/
theorem source_sylow_image :
    (MarkedLocal.sylowMap Q e h).range.map (quotientEquiv Q split d).toMonoidHom =
      Atlas.G2.unipotent := by
  rw [MarkedLocal.sylow_range Q e h split]
  exact (subgroup_images Q split d).1

/-- The source's first endpoint is short and the second long. -/
def forwardComparison (d₀ : RootData Q split F 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.amalgam (F := F)) :=
  (comparison Q e split d₀).trans CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.borelIso.symm

/-- Both original endpoints are explicitly reversed, with the whole Borel retained. -/
def reverseComparison (d₁ : RootData Q split F 1) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (RankTwoAmalgam.ofSubgroups (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F))
      (Atlas.G2.borel (K := F)) Atlas.G2.LieParabolicSetup.parabolic₁
      Atlas.G2.LieParabolicSetup.borel_le_parabolic₂ Atlas.G2.LieParabolicSetup.borel_le_parabolic₁) :=
  comparison Q e split d₁

/-- The original/geometric source marking reaches the actual null-plane and
singular-point stabilizers, with both squares and the whole overlap. -/
def geometricComparison (d₀ : RootData Q split F 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricAmalgam (F := F)) :=
  (forwardComparison Q e split d₀).trans
    CFSG.Quasithin.ChapterF.GreenBook.LieModels.G2.geometricIso

@[simp] theorem forwardComparison_left_apply (d₀ : RootData Q split F 0) (a : parabolic L S 0) :
    ((forwardComparison Q e split d₀).left a : Atlas.G2.Model F) =
      quotientEquiv Q split d₀ ((e.left a : Q.tits.standardParabolic {Q.simple 0}) : X ⧸ Q.D) := rfl

@[simp] theorem geometricComparison_left_apply (d₀ : RootData Q split F 0) (a : parabolic L S 0) :
    ((geometricComparison Q e split d₀).left a : Atlas.G2.Model F) =
      quotientEquiv Q split d₀ ((e.left a : Q.tits.standardParabolic {Q.simple 0}) : X ⧸ Q.D) := rfl

@[simp] theorem forwardComparison_middle_apply (d₀ : RootData Q split F 0) (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((forwardComparison Q e split d₀).middle b : Atlas.G2.Model F) =
      quotientEquiv Q split d₀ (e.middle b : X ⧸ Q.D) := rfl

@[simp] theorem geometricComparison_middle_apply (d₀ : RootData Q split F 0) (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((geometricComparison Q e split d₀).middle b : Atlas.G2.Model F) =
      quotientEquiv Q split d₀ (e.middle b : X ⧸ Q.D) := rfl

@[simp] theorem forwardComparison_right_apply (d₀ : RootData Q split F 0) (a : parabolic L S 1) :
    ((forwardComparison Q e split d₀).right a : Atlas.G2.Model F) =
      quotientEquiv Q split d₀ ((e.right a : Q.tits.standardParabolic {Q.simple 1}) : X ⧸ Q.D) := rfl

@[simp] theorem geometricComparison_right_apply (d₀ : RootData Q split F 0) (a : parabolic L S 1) :
    ((geometricComparison Q e split d₀).right a : Atlas.G2.Model F) =
      quotientEquiv Q split d₀ ((e.right a : Q.tits.standardParabolic {Q.simple 1}) : X ⧸ Q.D) := rfl

section GeneratedSource
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  (d₀ : RootData Q₀ split₀ F shortIndex)

/-- Specialization to the literal generated source quotient, preserving its
original quotient and both endpoint representatives. -/
def originalComparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F shortIndex) :=
  comparison Q₀ (originalMarkedIso Q₀) split₀ d₀

/-- The original left representative follows its literal inclusion and quotient. -/
@[simp] theorem originalComparison_left_apply (a : parabolic L S 0) :
    ((originalComparison Q₀ split₀ d₀).left a : Atlas.G2.Model F) =
      quotientEquiv Q₀ split₀ d₀
        (Q₀.q ⟨a, parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison, comparison_left_apply, originalMarkedIso_left_apply]

/-- The entire original overlap follows that same literal quotient. -/
@[simp] theorem originalComparison_middle_apply
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison Q₀ split₀ d₀).middle b : Atlas.G2.Model F) =
      quotientEquiv Q₀ split₀ d₀
        (Q₀.q ⟨b, parabolic_le_generated 0 b.property.1⟩) := by
  rw [originalComparison, comparison_middle_apply, originalMarkedIso_middle_apply]

/-- The original right endpoint retains its own literal inclusion. -/
@[simp] theorem originalComparison_right_apply (a : parabolic L S 1) :
    ((originalComparison Q₀ split₀ d₀).right a : Atlas.G2.Model F) =
      quotientEquiv Q₀ split₀ d₀
        (Q₀.q ⟨a, parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison, comparison_right_apply, originalMarkedIso_right_apply]
end GeneratedSource
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.G2Presentation
