module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.NativeAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SourceAssembly

/-!
# Original 11.1.5 with the fixed-summand obligation discharged

The genuine preceding 11.1.3 component input gives 11.1.4 on the actual flag.
The intrinsic point classifiers supply its blocks and seed span. NativeAssembly
proves fixed-center control, the Cartan--TI construction and exceptional-case
exclusion with the full native coverage theorem instantiated. The resulting
11.1.5 alternative has no native-cover or fixed-summand premise.

The preceding intrinsic classifiers and original 11.0.4/component/flag inputs
retain their existing producers; qt-d-1222-natural-normalizer-source owns their
final assembly. This theorem completes the fixed-summand owner's local chain,
not the unconditional preceding-source development.
Source: Aschbacher--Smith 11.1.3--5, printed pp.765--766, with the corrected
omega-center calculation described in docs/quasithin-proof-basis.md.
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

/-- The original point-radical conclusion from the genuine preceding intrinsic
and source inputs. All fixed-summand and native-model premises are discharged. -/
theorem chosen_source_11_1_5_of_intrinsic
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
  exact chosen_radicalAlternative D S f hn
    (fun he => (PointBlocks.Nonlinear.point_blocks_of_intrinsic D S hlinear hsymplectic f he).2)
    hline hres hcubic

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
