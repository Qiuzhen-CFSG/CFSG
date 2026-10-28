module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.SingleMoved
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.DoubleMoved
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.FamilyGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal

/-!
# Construction of the source mixed-factor geometry

A single source member and a double source member construct every field of
MixedLocal.RealizedFactors on the same actual residual pair. The family gives
normalizers and quotient indices, and the new fixed-space applications give
all literal commutator lines. The source adapter also constructs the mixed
Configuration from the original empty-family branch and its earlier universal
implications, retaining the separate small-center exclusion.

Source: Aschbacher--Smith, 15.4.18, pp.1162--1163.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup LocalSetup.SourceWitnesses
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_mixed_realized {κ : GroupClass}
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    {T : Sylow 2 G} {Y X M₁ M₂ : Subgroup G}
    (hY : Input κ T M₁ Y 1) (hX : Input κ T M₂ X 2) (p : Pair T M₂ X)
    (uniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (uniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂) (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    Nonempty (RealizedFactors T Y X M₁ M₂ p.quotient.factor) := by
  obtain ⟨PY,hPY⟩ := source_member_baumann_sylow hB hY
  obtain ⟨PX,hPX⟩ := source_member_baumann_sylow hB hX
  obtain ⟨t,ht,_,_,hnt⟩ := p.quotient.interchange
  obtain ⟨hy,hdy,hcy⟩ := source_single_fixed_geometry hB hY
  obtain ⟨hx,hwhole,hwholeDis,hlineDis⟩ := p.source_double_fixed_geometry hX
  refine ⟨{
    maximal₁ := hY.maximal
    maximal₂ := hX.maximal
    different := hne
    sylow_le₁ := hY.sylow_le
    sylow_le₂ := hX.sylow_le
    normalizer₁ := (source_member_normalizer hY).symm
    normalizer₂ := (source_member_normalizer hX).symm
    unique₁ := uniqueY
    unique₂ := uniqueX
    product := p.quotient.factor_generate hX
    pairAction := p.quotient.action
    swapper := t
    swapper_mem := ht
    swapper_moves := hnt
    baumann_invariant := p.baumann false
    thompson_commutator₁ := ?_
    thompson_commutator₂ := p.thompson_commutator hX false
    factor_core_index₁ := ?_
    factor_core_index₂ := p.quotient.factor_quotient_card false
    earlierSylow₁ := PY
    earlierSylow₁_image := hPY
    earlierSylowX := PX
    earlierSylowX_image := hPX
    single_split₁ := hy
    single_disjoint₁ := hdy
    single_card₁ := hcy
    single_split₂ := (hx false).1
    single_disjoint₂ := (hx false).2.1
    single_card₂ := (hx false).2.2
    double_split := hwhole
    double_disjoint := hwholeDis
    lines_disjoint := hlineDis
    central_fixed_card := (centralizer_card_two_of_hyperplane hZ (source_double_hyperplane hX)).1
  }⟩
  · simpa only [ChapterB.thompsonJ_zero] using YFamily.commutator_eq hY.member
  · simpa only [Subgroup.index,pow_one] using hY.quotient_card


/-- The original empty-family branch constructs the same mixed configuration;
only the independent small-center exclusion and the two branch parameters
remain, alongside the complete earlier universal source implications. -/
theorem source_mixed_configuration_of_empty
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (hD14 : RatioSource.InsideCore.EarlierD14Sylow.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (Theory.GroupTheory.maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)))
    {M₁ M₂ Y X : Subgroup G}
    (hY : Input KnownSimple.IsKnownSimple T M₁ Y 1)
    (hX : Input KnownSimple.IsKnownSimple T M₂ X 2) (hne : M₁ ≠ M₂) :
    ∃ p : Pair T M₂ X, Nonempty (RealizedFactors T Y X M₁ M₂ p.quotient.factor) ∧
      Configuration KnownSimple.IsKnownSimple T Y X M₂ p.quotient.factor := by
  obtain ⟨p⟩ := exists_pair hX
  have uniqueY := (source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M₁ ⟨hY.maximal,hY.sylow_le⟩ Y hY.member hY.member_le).2
  have uniqueX := (source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M₂ ⟨hX.maximal,hX.sylow_le⟩ X hX.member hX.member_le).2
  have hZ := (source_lemma_15_4_14_of_large_center hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany hlarge).1
  obtain ⟨d⟩ := source_mixed_realized hB hY hX p uniqueY uniqueX hne hZ
  refine ⟨p,⟨d⟩,MixedLocal.construct hG T d ?_⟩
  intro M hM hTM
  exact source_lemma_15_4_16 hA hC h311 hD15 hD14 h29 hB hG T hempty hmany M ⟨hM,hTM⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
