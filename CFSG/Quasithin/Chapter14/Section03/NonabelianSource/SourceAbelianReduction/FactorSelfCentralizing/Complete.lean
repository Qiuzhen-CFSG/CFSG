module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.FactorWitness
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.FourCenter
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.TerminalFour
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Sporadic.Source

/-!
# Original factor self-centralization

The marked centralizer contains the genuine point-block C-component.
The elementary factor is a witness for the existential condition in 1.2.11;
this avoids requiring a direct residual calculation on the original seed.
The actual quotient-centralizer extension excludes every resulting 1.1.5
model, contradicting strict enlargement of the factor's centralizer.

Source: Aschbacher--Smith, 14.3.20, pp.997--998, using 1.2.11(a), p.508.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem modelExclusionSource_of_source_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) : ModelExclusionSource F (sourceResidual M Mc) := by
  exact modelExclusionSource_of_source_inputs_and_local_sporadic
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (quotientCentralizerSource_of_source_hypotheses
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs)
    (sporadicExclusionSource_of_source_inputs
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs)

theorem factorSelfCentralizing_of_source_hypotheses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) : FactorSelfCentralizing F (sourceResidual M Mc) := by
  intro A hEA hAR hVA hAc hc8 hAN
  let := hEA
  have hfactor : ElementaryFactor F (sourceResidual M Mc) A :=
    ⟨hEA, hAR, hVA, hAc, hc8, hAN⟩
  have hAC : A ≤ centralizer (A : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  by_contra hneA
  have hlt : A < centralizer (A : Set G) := lt_of_le_of_ne hAC hneA
  obtain ⟨P⟩ := markedPoint_of_strict_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hAR hVA hAc hc8 hAN hlt
  obtain ⟨z, _, hz⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hg := fourCenterSource_of_source_hypotheses
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hfactor hlt P z hz
  have hSylow := (global_sylow_of_fourCenterGeometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hAR hVA hAc hc8 hAN hlt P z hz hg).2
  have hcore := source_global_core_eq hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs A hfactor hlt P z hz hSylow
  have hcontaining := source_containing_component hG T hempty hM hu hmany hcard e hnot F
    hne g hgP hgH hs hfactor hlt P z hz hg hSylow
  have hVT := (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e).seed_le_sylow
  exact modelExclusionSource_of_source_hypotheses
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A hfactor hlt P z hz
    hg hSylow hcore
    (P.classifiedComponent_of_factor_witness hG hAc hVA hVT z hz hSylow hcore hcontaining)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
