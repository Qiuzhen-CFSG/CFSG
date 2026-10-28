module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.CoverAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SourceAssembly

/-!
# The original point-radical consumer with the uniform native input

The repaired source 11.1.4 supplies normalizer control on the original flag.
The existing intrinsic point classifiers supply the actual blocks and
V=V_M; the corrected cohomology calculation supplies the omega-center
splitting. CoverAssembly then proves the full 11.1.5 radical alternative,
including SL3(4), without a fixed-summand or local-placement callback.

The intrinsic inputs retain qt-c132-nonbinary-symplectic and
qt-c134-nonbinary-linear-three-source. The earlier flag, component and
11.0.4 identities retain qt-d-1222-natural-local-geometry and the final
assembler qt-d-1222-natural-normalizer-source. The uniform native cover
and its symmetry input retain qt-model-j4-elementary-normalizer-cover and
qt-model-j4-large-center-radicals; their final application remains with
qt-d-1222-natural-point-fixed-summand. This is a conditional endpoint,
not an assertion that those independent native inputs have been proved.

Source: Aschbacher--Smith 11.1.3--5, printed pp.765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
open Centralizer
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


include hlinear hsymplectic

/-- The full original 11.1.5 conclusion, with only the named independent
native cover and preceding intrinsic/source inputs remaining. -/
theorem chosen_source_11_1_5_of_intrinsic_and_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
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
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  have hn := chosen_source_11_1_4_of_component D S f hunique
  exact chosen_radicalAlternative_of_elementary_cover C eC hcover D S f hn
    (fun he => (PointBlocks.Nonlinear.point_blocks_of_intrinsic D S hlinear hsymplectic f he).2)
    hline hres hcubic

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
