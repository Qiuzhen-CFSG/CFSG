module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear.Doubled
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear.Initial
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology

/-!
# The linear point classification in the original radical alternative

Only the section data and radical inequalities of the intrinsic C.1.34
classifier are required inside the literal LR₁, with
S'=T∩LR₁. The initial-module point-fixer calculation excludes every nonblock
radical inequality without a whole-core model premise;
shortness then gives the original V=V_M. The last theorem feeds that
recognition into RadicalAssembly and discharges its center premise using
the corrected cohomology theorem.

The intrinsic input is produced by qt-c134-nonbinary-linear-three-source.
PointModuleCases omits the disputed whole-core fixed-factor centrality and
the unused upper sections; pointModuleCases_of_alternatives retains an
adapter from the existing full interface.
The nonlinear recognition, G₂ exclusion and fixed-summand input remain
with qt-d-1222-natural-normalizer-source and its retained external producers;
qt-d-1222-natural-local-geometry retains preceding-source discharge. These
conditional applications do not assert completion of 11.1.5.
Source: Aschbacher--Smith, C.1.34, pp.136--137, and 11.1.5, pp.765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (hintrinsic : ∀ R U : Subgroup G,
    LinearThreeMSPair KnownSimple.IsKnownSimple L R S.field.degree S.field.Carrier →
    Chapter1.IsSylowIn 2 U (L ⊔ R) → R ≤ U →
    ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier),
      PointModuleCases D S R U e)

include hintrinsic

/-- The source point recognition, with all local inputs to C.1.34 discharged. -/
theorem point_recognition_of_intrinsic : LinearPointRecognition D S := by
  intro m f hm
  obtain ⟨e,he⟩ := hintrinsic (f.Ri 0) ((T : Subgroup G) ⊓ (L ⊔ f.Ri 0))
    (point_linearThreeMSPair D S m f hm)
    (pointSylow_isSylowIn D S f) (radical_le_pointSylow D S f)
  rcases he with hb | ⟨_,hne⟩ | hz
  · exact hb
  · exact (point_not_MSNotCentralizerCore D S m f hm hne).elim
  · exact (pointSylow_omega_not_central D S m f hz).elim

/-- The escaping original linear point gives both the actual block and V=V_M. -/
theorem escaping_point_block
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m))
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
      ChapterC.IsSL3EvenBlock L S.field.degree := by
  have hb := point_recognition_of_intrinsic D S hintrinsic m f
    (point_msPair D S f hescape)
  exact ⟨(point_blocks_with_span D (Or.inl hb)).1,hb⟩

/-- The literal RadicalAssembly consumer now needs only the intrinsic linear
classifier, the two nonlinear rows and preservation of the fixed center.
The point-radical exclusions and corrected cohomology premise are proved. -/
theorem radicalAlternative_of_intrinsic_linear
    (hsymplectic : SymplecticPointRecognition D S)
    (hexceptional : ExceptionalPointExclusion D S)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hfixed : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  PointCohomology.radicalAlternative D S f
    (chosen_point_blocks_of_recognition D S
      (point_recognition_of_intrinsic D S hintrinsic) hsymplectic hexceptional f) hfixed

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Linear
