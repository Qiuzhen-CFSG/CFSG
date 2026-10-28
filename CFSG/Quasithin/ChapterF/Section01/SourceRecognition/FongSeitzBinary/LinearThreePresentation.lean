module
public import Theory.SpecificGroups.PSL3.RootPresentationRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniversalSimpleSocle
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree

/-!
# The original F.1.1 marking from explicit A₂ root data

For the same independently marked finite quotient used by MarkedLocal, the
faithfulness theorem for the genuine original F.1.1 overlap forces the Borel
core, hence the ambient center, to vanish. Six-root relations, generation,
positive generation and two negative-root placements then give the actual
PSL₃ flag comparison. Both endpoint squares and the whole common Borel use
one ambient equivalence composed with the supplied source marking.

The point index gives either orientation. No simplicity, order formula,
Cartan comparison, or parabolic equality of the unknown quotient is an input.
The construction of these six compatible root maps remains with the source
recognition assembly; this conditional theorem does not establish that input
or equality of the distinct local factors with model Levi factors.

Source: DGS, Groups and Graphs, Theorem D, p.224; Aschbacher–Smith F.1.1,
F.1.9 and F.1.11, pp.259–262; Steinberg §6, pp.71–74.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearThreePresentation
variable {G X F : Type*} [Group G] [Group X] [Field F]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)

include e h in
/-- Genuine F.1.1 overlap faithfulness transfers to this independently marked
quotient. In particular this applies to the universal geometric marking. -/
theorem borel_core_eq_bot : Q.tits.B.normalCore = ⊥ := by
  let α := RankTwoAmalgam.ofSubgroups (parabolic L S 0)
    (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right
  let c := (standardCompletion Q).comapIso e
  let u := RankTwoAmalgam.Universal.completion α c
  have hu : u.middle.range.normalCore = ⊥ := by
    have hu := originalUniversal_overlap_core_eq_bot h
    rw [RankTwoAmalgam.Universal.overlap_eq α (inclusion_injective inf_le_left)
      (inclusion_injective inf_le_right)] at hu
    exact hu
  have hc := c.middle_normalCore_eq_bot_of_model u hu
  simpa only [c, RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range,
    standardCompletion_middle_range] using hc

variable (split : SplitData Q.tits)

include e h split in
/-- The genuine original overlap discharges centerlessness, independently
of any root-field compatibility or recognition conclusion. -/
theorem center_eq_bot : center (X ⧸ Q.D) = ⊥ :=
  split.center_eq_bot_of_borel_core (borel_core_eq_bot Q e h)

variable [Finite F] [CharP F 2] {pointIndex : Fin 2}
  (d : RootData Q split F pointIndex)

/-- The actual quotient equivalence, preserving all six roots and parameters. -/
def quotientEquiv : (X ⧸ Q.D) ≃* PSL(3,F) :=
  rootEquiv Q split d (borel_core_eq_bot Q e h)

omit [CharP F 2] in
@[simp] theorem quotientEquiv_root (r : Theory.SpecificGroups.LinearHigher.Root 3) (a : F) :
    quotientEquiv Q e h split d (d.x r a) =
      Theory.SpecificGroups.LinearHigher.projectiveRoot r a :=
  rootEquiv_root Q split d _ r a

/-- The actual source U, full Borel, and both marked vertices, including reverse
orientation, are compared by this one root-preserving equivalence. -/
theorem subgroup_images :
    split.U.map (quotientEquiv Q e h split d).toMonoidHom = unipotent F ∧
    Q.tits.B.map (quotientEquiv Q e h split d).toMonoidHom = Matrix.PSL3.LinearThree.borel F ∧
    (Q.tits.standardParabolic {Q.simple pointIndex}).map
      (quotientEquiv Q e h split d).toMonoidHom = pointParabolic F ∧
    (Q.tits.standardParabolic {Q.simple (1 - pointIndex)}).map
      (quotientEquiv Q e h split d).toMonoidHom = lineParabolic F :=
  ⟨rootEquiv_unipotent Q split d _, rootEquiv_borel Q split d _,
    rootEquiv_point Q split d _, rootEquiv_line Q split d _⟩

/-- Restrict the constructed ambient equivalence and compose with the literal
original/geometric source marking, retaining both inclusion squares. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F pointIndex) :=
  e.trans (markedIso Q split d (borel_core_eq_bot Q e h))

@[simp] theorem comparison_left_apply (a : parabolic L S 0) :
    ((comparison Q e h split d).left a : PSL(3,F)) =
      quotientEquiv Q e h split d ((e.left a : Q.tits.standardParabolic {Q.simple 0}) :
        X ⧸ Q.D) := rfl

/-- The formula holds on the entire overlap, rather than only its Sylow. -/
@[simp] theorem comparison_middle_apply
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e h split d).middle b : PSL(3,F)) =
      quotientEquiv Q e h split d (e.middle b : X ⧸ Q.D) := rfl

@[simp] theorem comparison_right_apply (a : parabolic L S 1) :
    ((comparison Q e h split d).right a : PSL(3,F)) =
      quotientEquiv Q e h split d ((e.right a : Q.tits.standardParabolic {Q.simple 1}) :
        X ⧸ Q.D) := rfl

/-- Literal left endpoint square for the original inclusion amalgam. -/
theorem comparison_left_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e h split d).left ⟨b, b.property.1⟩ =
      (flagAmalgam F pointIndex).left ((comparison Q e h split d).middle b) :=
  (comparison Q e h split d).left_commutes b

/-- Literal right endpoint square for that same whole original overlap. -/
theorem comparison_right_square (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e h split d).right ⟨b, b.property.2⟩ =
      (flagAmalgam F pointIndex).right ((comparison Q e h split d).middle b) :=
  (comparison Q e h split d).right_commutes b

/-- The common Borel formula uses exactly MarkedLocal's full-overlap map. -/
theorem comparison_commonBorel_apply (b : commonBorel L S) :
    ((comparison Q e h split d).middle
      ((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm) b) : PSL(3,F)) =
      quotientEquiv Q e h split d (MarkedLocal.borelMap Q e h b) := rfl

/-- The original Sylow has exactly the model unipotent image, under the
same common-Borel/quotient map used on every original endpoint. -/
theorem source_sylow_image :
    (MarkedLocal.sylowMap Q e h).range.map (quotientEquiv Q e h split d).toMonoidHom =
      unipotent F := by
  rw [MarkedLocal.sylow_range Q e h split]
  exact (subgroup_images Q e h split d).1

/-- At point index zero the target is the existing concrete LinearThree amalgam. -/
def forwardComparison (d₀ : RootData Q split F 0) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.amalgam F) :=
  comparison Q e h split d₀

/-- At point index one the actual flag vertices and inclusions are reversed. -/
def reverseComparison (d₁ : RootData Q split F 1) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (RankTwoAmalgam.ofSubgroups (lineParabolic F) (Matrix.PSL3.LinearThree.borel F) (pointParabolic F)
      (map_mono inf_le_right) (map_mono inf_le_left)) :=
  comparison Q e h split d₁

section GeneratedSource
variable (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
  (d₀ : RootData Q₀ split₀ F pointIndex)

/-- Specialization to the literal generated source quotient. Its Borel
faithfulness is discharged from F.1.1, rather than supplied as an extra premise. -/
def originalComparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F pointIndex) :=
  comparison Q₀ (originalMarkedIso Q₀) h split₀ d₀

/-- The original left representative follows its literal inclusion and quotient. -/
@[simp] theorem originalComparison_left_apply (a : parabolic L S 0) :
    ((originalComparison h Q₀ split₀ d₀).left a : PSL(3,F)) =
      quotientEquiv Q₀ (originalMarkedIso Q₀) h split₀ d₀
        (Q₀.q ⟨a, parabolic_le_generated 0 a.property⟩) := by
  rw [originalComparison, comparison_left_apply, originalMarkedIso_left_apply]

/-- The entire original overlap follows that same literal quotient. -/
@[simp] theorem originalComparison_middle_apply
    (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalComparison h Q₀ split₀ d₀).middle b : PSL(3,F)) =
      quotientEquiv Q₀ (originalMarkedIso Q₀) h split₀ d₀
        (Q₀.q ⟨b, parabolic_le_generated 0 b.property.1⟩) := by
  rw [originalComparison, comparison_middle_apply, originalMarkedIso_middle_apply]

/-- The original right endpoint retains its own literal inclusion. -/
@[simp] theorem originalComparison_right_apply (a : parabolic L S 1) :
    ((originalComparison h Q₀ split₀ d₀).right a : PSL(3,F)) =
      quotientEquiv Q₀ (originalMarkedIso Q₀) h split₀ d₀
        (Q₀.q ⟨a, parabolic_le_generated 1 a.property⟩) := by
  rw [originalComparison, comparison_right_apply, originalMarkedIso_right_apply]
end GeneratedSource
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearThreePresentation
