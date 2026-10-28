module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootGeneratedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# A₂ presentation comparison from canonical source root ranges

For the same independently marked perfect source quotient, global generation
is a consequence of covering its actual Weyl-conjugate roots. Positive
root generation follows from covering the ordered positive factors and
placing the positive parameters in U. These two premises of the proved
A₂ presentation comparison are therefore discharged here.

The field, all six parameter maps, every mixed Steinberg relation, the
canonical-root range coverage and both negative-root placements remain
explicit. They are genuine remaining source-reconstruction obligations;
this conditional comparison is not a proof of the A₂ source row. Its target
retains either orientation, the whole Borel and both endpoint squares.

Source: DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D, p.224;
Carter 2.5.10–2.5.17 for the ordered products; Steinberg §6, pp.71–74
for the independently proved finite A₂ presentation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.LinearHigher
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootGeneration
open Matrix.PSL3.RootPresentationRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearThreeCanonicalRoots
variable {G X F : Type*} [Group G] [Group X] [Field F]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (hp : ∀ i, Group.IsPerfect (L i))
  (split : SplitData Q.tits) (x : Root 3 → F → X ⧸ Q.D)

omit [Field F] in
/-- Covering the actual positive factors and staying in U gives exact positive closure. -/
theorem positiveClosure_eq
    (hmem : ∀ r a, r.val.1 < r.val.2 → x r a ∈ split.U)
    (hcover : ∀ A ∈ orderedRoots Q split false (rotationOrder Q),
      ∃ r : Root 3, r.val.1 < r.val.2 ∧ (A : Set (X ⧸ Q.D)) ⊆ Set.range (x r)) :
    positiveClosure x = split.U := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g ⟨r,a,hr,rfl⟩
    exact hmem r a hr
  · apply unipotent_le_of_orderedRoots_le Q split _ false
    intro A hA g hg
    obtain ⟨r,hr,hs⟩ := hcover A hA
    obtain ⟨a,ha⟩ := hs hg
    exact subset_closure ⟨r,a,hr,ha.symm⟩

variable {pointIndex : Fin 2}
  (hx : Relations x)
  (hcover : ∀ (i : Fin 2) (w : Weyl Q),
    ∃ r : Root 3,
      (rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) : Set (X ⧸ Q.D)) ⊆
        Set.range (x r))
  (hmem : ∀ r a, r.val.1 < r.val.2 → x r a ∈ split.U)
  (hpositive : ∀ A ∈ orderedRoots Q split false (rotationOrder Q),
    ∃ r : Root 3, r.val.1 < r.val.2 ∧ (A : Set (X ⧸ Q.D)) ⊆ Set.range (x r))
  (hpoint : x (root (2 : Fin 3) 1 (by decide)) 1 ∈
    Q.tits.standardParabolic {Q.simple pointIndex})
  (hline : x (root (1 : Fin 3) 0 (by decide)) 1 ∈
    Q.tits.standardParabolic {Q.simple (1 - pointIndex)})

/-- Construct the presentation input, proving both generation fields from actual roots. -/
@[expose] def rootData : RootData Q split F pointIndex where
  x := x
  relations := hx
  generate := MarkedLocal.root_parameters_generate Q e h hp split x hcover
  positive := positiveClosure_eq Q split x hmem hpositive
  negative_point := hpoint
  negative_line := hline

variable [Finite F] [CharP F 2]

/-- A literal conditional regular-branch comparison for the original inclusion amalgam. -/
def comparison : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (flagAmalgam F pointIndex) :=
  LinearThreePresentation.comparison Q e h split
    (rootData Q e h hp split x hx hcover hmem hpositive hpoint hline)

omit [CharP F 2] in
/-- The constructed quotient map preserves every supplied root parameter. -/
theorem quotientEquiv_root (r : Root 3) (a : F) :
    LinearThreePresentation.quotientEquiv Q e h split
      (rootData Q e h hp split x hx hcover hmem hpositive hpoint hline) (x r a) =
        projectiveRoot r a :=
  LinearThreePresentation.quotientEquiv_root Q e h split _ r a

/-- The entire original overlap follows the same quotient equivalence. -/
theorem comparison_middle_apply (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).middle b : PSL(3,F)) =
      LinearThreePresentation.quotientEquiv Q e h split
        (rootData Q e h hp split x hx hcover hmem hpositive hpoint hline)
        (e.middle b : X ⧸ Q.D) :=
  LinearThreePresentation.comparison_middle_apply Q e h split _ b

/-- Both original endpoint inclusion squares commute on every overlap element. -/
theorem comparison_squares (b : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    (comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).left ⟨b,b.property.1⟩ =
      (flagAmalgam F pointIndex).left
        ((comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).middle b) ∧
    (comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).right ⟨b,b.property.2⟩ =
      (flagAmalgam F pointIndex).right
        ((comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).middle b) :=
  ⟨(comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).left_commutes b,
    (comparison Q e h hp split x hx hcover hmem hpositive hpoint hline).right_commutes b⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearThreeCanonicalRoots
