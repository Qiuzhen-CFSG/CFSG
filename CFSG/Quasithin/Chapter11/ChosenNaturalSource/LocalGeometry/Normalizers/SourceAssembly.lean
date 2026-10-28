module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan

/-!
# Source normalizers with only the remaining external inputs

The unique actual flag transports the repaired displacement-plane geometry
to any supplied invariant flag, proving both clauses of 11.1.4 from the
permitted 11.1.3 component premise. In 11.1.5 the local linear exclusions,
nonbinary G₂ exclusion, corrected cohomology, and proved fixed-summand cases
leave only the intrinsic classifiers and the field-four linear fixed-summand
case. The literal line-action theorem gives both clauses of 11.2.3.

The two intrinsic inputs are owned by qt-c132-nonbinary-symplectic and
qt-c134-nonbinary-linear-three-source. The SL₃(4) fixed-summand input belongs
to qt-d-1222-natural-point-fixed-summand, and the shared line application
remains with qt-d-1222-natural-line-action. This task retains their final
discharge. The preceding component and 11.0.4 inputs are assembled by
qt-d-1222-natural-local-geometry. This is a conditional source assembly,
not a completed unguarded source theorem.
Source: Aschbacher--Smith 11.1.4--5 and 11.2.3, pp.765--766,768--769.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open ChapterC.RankTwo.NonbinarySymplectic
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (hlinear : ∀ R U : Subgroup G,
    LinearThreeMSPair KnownSimple.IsKnownSimple L R S.field.degree S.field.Carrier →
    Chapter1.IsSylowIn 2 U (L ⊔ R) → R ≤ U →
    ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier), PointBlocks.Linear.PointModuleCases D S R U e)
  (hsymplectic : ∀ (R : Subgroup G),
    Input (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) S.field.degree S.field.Carrier →
      ChapterC.IsSp4FourBlock (L.subgroupOf (L ⊔ R)))


/-- The repaired plane geometry gives both 11.1.4 clauses on the supplied flag.
Only the genuine earlier 11.1.3 component-uniqueness hypothesis remains. -/
theorem chosen_source_11_1_4_of_component
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1)) :
    Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)) := by
  obtain ⟨g,hg,_,_,_,hc⟩ := exists_marked_flag_with_normalizerControl D S c
  have hs : f.space = g.space :=
    funext fun i => hg i (f.space i) (f.dimension i) (f.invariant i)
  have he : f = g := by cases f; cases g; cases hs; rfl
  subst g
  exact hc hunique

include hlinear hsymplectic

/-- All local 11.1.5 branches are assembled; the fixed-summand input is
restricted to its remaining original SL₃(4) case. -/
theorem chosen_source_11_1_5_of_intrinsic_and_linear_four
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hfour : ∀ (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
      (g : InvariantFlag (.sl3 m)), S.field.degree = 2 →
      (¬ normalizer (g.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      ChapterC.IsSL3EvenBlock L S.field.degree →
      radicalOmegaCenter (g.Ri 0) = g.Vi 0 ⊔ radicalFixedCenter (g.Ri 0) L →
      normalizer (g.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (g.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  have hn := chosen_source_11_1_4_of_component D S f hunique
  by_cases hdegree : S.field.degree = 2
  · cases c with
    | sl3 m =>
      apply PointCohomology.radicalAlternative D S f
        (PointBlocks.Nonlinear.point_blocks_of_intrinsic D S hlinear hsymplectic f)
      intro he _ hc
      have hb := PointBlocks.Linear.point_recognition_of_intrinsic D S hlinear m f
        (PointBlocks.point_msPair D S f he)
      exact hfour m f hdegree he hb hc
    | sp4 m =>
      exact PointBlocks.Nonlinear.sp4_radicalAlternative_of_intrinsic D S hsymplectic m f hn
    | g2 m => exact PointBlocks.Nonlinear.point_g2_radicalAlternative D S m f
  · exact PointBlocks.Nonlinear.radicalAlternative_of_intrinsic_degree_ne_two D S
      hlinear hsymplectic f hdegree hn hline hres hcubic

/-- Both normalizer restrictions, the exact radical alternative, and both
11.2.3 clauses for the same original flag, with final source inputs explicit. -/
theorem chosen_source_normalizers_of_intrinsic_and_linear_four
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hfour : ∀ (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
      (g : InvariantFlag (.sl3 m)), S.field.degree = 2 →
      (¬ normalizer (g.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      ChapterC.IsSL3EvenBlock L S.field.degree →
      radicalOmegaCenter (g.Ri 0) = g.Vi 0 ⊔ radicalFixedCenter (g.Ri 0) L →
      normalizer (g.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (g.Ri 0) L : Set G))
    {X : Subgroup G} (hX : IsCartan T L X) :
    Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)) ∧
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree ∧
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) := by
  have hr := chosen_source_11_1_5_of_intrinsic_and_linear_four D S hlinear hsymplectic f
    hunique hline hres hcubic hfour
  exact ⟨chosen_source_11_1_4_of_component D S f hunique,hr,
    chosen_source_11_2_3_of_intrinsic_sp4_classification D S f hX
      (hsymplectic (T : Subgroup G)) hr⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
