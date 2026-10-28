module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Symplectic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Four
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear.Source

/-!
# Applying nonlinear point recognition to the original radical alternative

The actual symplectic quotient and block model are transported through LR₁.
Together with the proved local linear exclusions, the intrinsic classifiers
supply both classical point branches. At degree two the exceptional branch
is excluded by reciprocal critical root actions, so the original cohomology
assembly needs only preservation of the fixed center.

The two intrinsic classification inputs remain with their named producers;
this owner retains their final application. The fixed-center and earlier
source inputs retain their original owners. No conditional result here is
asserted as the completed 11.1.5 theorem.
Source: Aschbacher--Smith 11.1.5, pp.765--766.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.RankTwo.NonbinarySymplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (hlinear : ∀ R U : Subgroup G,
    LinearThreeMSPair KnownSimple.IsKnownSimple L R S.field.degree S.field.Carrier →
    Chapter1.IsSylowIn 2 U (L ⊔ R) → R ≤ U →
    ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier), Linear.PointModuleCases D S R U e)
  (hsymplectic : ∀ (R : Subgroup G),
    Input (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) S.field.degree S.field.Carrier →
      ChapterC.IsSp4FourBlock (L.subgroupOf (L ⊔ R)))

include hlinear hsymplectic

/-- The actual three-family point conclusion at field four, with every local
classification premise supplied and the G₂ branch excluded. -/
theorem point_blocks_four_of_intrinsic (hfour : S.field.degree = 2)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (he : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) := by
  apply chosen_point_blocks_of_recognition D S
    (Linear.point_recognition_of_intrinsic D S hlinear)
    (symplectic_point_recognition_of_intrinsic D S hsymplectic) _ f he
  intro m f hm
  exact point_g2_four_false D S m f hm hfour

/-- RadicalAssembly's original field-four alternative, with the corrected
cohomology calculation discharged and only intrinsic/fixed-center inputs left. -/
theorem radicalAlternative_four_of_intrinsic (hfour : S.field.degree = 2)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  PointCohomology.radicalAlternative D S f
    (point_blocks_four_of_intrinsic D S hlinear hsymplectic hfour f) hfixed

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
