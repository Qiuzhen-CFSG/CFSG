module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.G2Exclusion
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SourceFamilies

/-!
# Point recognition and the original normalizer consumers

The general G₂ exclusion completes the local point-row selection. Applying
both shared intrinsic classifiers constructs the original classical blocks
and V=V_M. The corrected cohomology theorem supplies the omega-center identity.
The proved fixed-summand argument completes the symplectic branch and every
larger field degree; only its genuine SL₃(4) gap remains. The final application
feeds the literal radical alternative into both clauses of 11.2.3.

The explicit intrinsic inputs belong to qt-c132-nonbinary-symplectic and
qt-c134-nonbinary-linear-three-source. Fixed-center discharge belongs to
qt-d-1222-natural-point-fixed-summand; line-action discharge remains with
qt-d-1222-natural-line-action. This normalizer task retains final assembly,
and qt-d-1222-natural-local-geometry supplies the permitted preceding source
identities. These conditional consumers are not completed source theorems.
Source: Aschbacher--Smith 11.1.5 and 11.2.3, pp.765--766,768--769.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative Pointwise commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.G2MS
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
open ChapterC.RankTwo.NonbinarySymplectic
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter12.Section02
open scoped MatrixGroups
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

/-- Point recognition in every nonbinary degree: all local hypotheses and
exceptional exclusions are discharged; only the two intrinsic producers remain. -/
theorem point_blocks_of_intrinsic
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (he : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) :=
  chosen_point_blocks_of_recognition D S
    (Linear.point_recognition_of_intrinsic D S hlinear)
    (symplectic_point_recognition_of_intrinsic D S hsymplectic)
    (exceptional_point_exclusion D S) f he

/-- The literal radical alternative with G₂ and corrected cohomology discharged. -/
theorem radicalAlternative_of_intrinsic
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  PointCohomology.radicalAlternative D S f
    (point_blocks_of_intrinsic D S hlinear hsymplectic f) hfixed

omit hlinear in
/-- The symplectic radical alternative needs no fixed-summand callback.
Its remaining normalizer control is the permitted preceding 11.1.4 input. -/
theorem sp4_radicalAlternative_of_intrinsic
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G))) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  by_cases he : normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)
  · exact Or.inl he
  have hb := symplectic_point_recognition_of_intrinsic D S hsymplectic m f
    (point_msPair D S f he)
  exact FixedSummand.Sp4.radicalAlternative D S m f hb hn
    (fun _ => PointCohomology.center_eq D S f (Or.inr hb))

/-- Above field four, the proved fixed-center source argument supplies the
literal 11.1.5 conclusion from the original earlier-source identities. -/
theorem radicalAlternative_of_intrinsic_degree_ne_two
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hdegree : S.field.degree ≠ 2)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  FixedSummand.chosen_radicalAlternative_of_degree_ne_two D S f hdegree hn
    (fun he => (point_blocks_of_intrinsic D S hlinear hsymplectic f he).2)
    hline hres hcubic

/-- The actual 11.1.5 and 11.2.3 consumer, including both line clauses.
The intrinsic classifiers and field-four fixed-center obligation retain their
external owners; final discharge stays with this normalizer-source task. -/
theorem source_11_1_5_and_11_2_3_of_intrinsic
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree ∧
    ((V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G))) := by
  have hr := radicalAlternative_of_intrinsic D S hlinear hsymplectic f hfixed
  exact ⟨hr,chosen_source_11_2_3_of_intrinsic_sp4_classification D S f hX
    (hsymplectic (T : Subgroup G)) hr⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
