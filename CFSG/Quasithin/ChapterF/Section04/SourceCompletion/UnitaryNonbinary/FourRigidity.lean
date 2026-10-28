module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourRootDefect
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRootGeneration

/-!
# Elimination of the nonbinary PSU₄ completion defect

The accepted full-overlap defect preserves the native roots and fixes the
full diagonal Cartan. Scalar rigidity makes both root actions pointwise
trivial; native root, Cartan and Weyl generation then makes the defect the
identity automorphism. Thus the literal marked rotation has fourth power
one in every completion under the genuine full-extension order bound.

This includes q = 4 and the degree-two outer action. Source:
Aschbacher–Smith F.4.10,16–17,24, printed pp.279,282–283,287.
Identification through the paired common cover is the subsequent step.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "J" => UnitaryFourFlag.form F σ hσ
local notation "π" => project F J

/-- Literal pointwise fixation of the two native relative simple roots. -/
def SimpleRootsFixed (a : MulAut (ProjectiveGroup m hm)) : Prop :=
  (∀ x : F, a (π (SmallCompletion.FourRoots.shortRoot F σ hσ x))=
    π (SmallCompletion.FourRoots.shortRoot F σ hσ x)) ∧
  (∀ x : UnitaryFourSylow.FixedField F σ,
    a (π (SmallCompletion.FourRoots.longRoot F σ hσ x))=
      π (SmallCompletion.FourRoots.longRoot F σ hσ x))

/-- Full-Cartan involutory defects fix the actual simple roots pointwise. -/
theorem constraints_fix_simpleRoots (a : MulAut (ProjectiveGroup m hm))
    (ha : SourceExtension.CartanFixedInvolution (point m hm) (plane m hm)
      (diagonalCartan m hm) a) : SimpleRootsFixed m hm a := by
  obtain ⟨hs,hl⟩ := constraints_preserve_simpleRoots m hm a ha
  exact SmallCompletion.FourRootRigidity.fixes_simpleRoots F σ hσ a ha.square
    (fun g hg => ha.fixes_cartan _ ⟨g,hg,rfl⟩) hs hl

/-- The proved Cartan/Weyl constraints force the native automorphism to be
identity, with no automorphism-classification premise. -/
theorem constraints_eq_one (a : MulAut (ProjectiveGroup m hm))
    (ha : SourceExtension.CartanFixedInvolution (point m hm) (plane m hm)
      (diagonalCartan m hm) a) : a=1 := by
  obtain ⟨hs,hl⟩ := constraints_fix_simpleRoots m hm a ha
  exact SmallCompletion.FourRootGeneration.projective_aut_eq_one F σ hσ a hs hl
    ha.fixes_point ha.fixes_plane (fun g hg => ha.fixes_cartan _ ⟨g,hg,rfl⟩)

/-- The actual marked Weyl relation holds in every completion satisfying
source F.4.24's full-extension order bound and whole-overlap hypothesis. -/
theorem rotation_fourth_eq_one (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : rotation m hm E c ^ 4=1 := by
  obtain ⟨a,ha,hfix⟩ := fourth_defect m hm hmgt E c ho hcard
  have he : a=1 := Subtype.ext (constraints_eq_one m hm a.val hfix)
  rw [←ha,he,map_one]
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
