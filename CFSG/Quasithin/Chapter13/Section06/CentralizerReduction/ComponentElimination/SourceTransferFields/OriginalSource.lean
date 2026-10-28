module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.DirectSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OriginalConsumers
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.SourceTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.Normalizer.ResidualBound
/-!
# Original marked source assembly for 13.6.17--19

The chosen source flag constructs the local Sylow and its index two in T,
characteristic two, reduced W_K, Baumann placement and the local residual
bound.  The proved original 13.6.14--15 supply component invariance and the
A5 seed exclusion. Replacement transport and characteristic strictness give
13.6.16; the complete A/C/B5, characteristic block-orbit and natural-section
Baumann theorems then finish the common noncentrality and field exclusions.

The only universal earlier Chapter 13 predicates are the genuine 13.3.2
normalization and 13.6.3(2) omega-centralizer theorem on every transported
SourceHypothesis. Their existing earlier-source owners retain final discharge.
The original FlagSource, EarlierLocal and fusion hypotheses remain exactly on
the source's chosen marking.  hL and hz specify the literal plus quotient maps.

Source: Aschbacher--Smith 13.6.17--19, printed pp.930--931.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ComponentSelection A5Module ComponentReduction InitialSieve
open ChapterB.QuasisimpleSource SourceContainment.RankTwo.LocalApplication
open RankOneBorel.Replacement.NaturalRecognition HigherFieldParabolics
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem noncentrality_and_field_exclusions_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤ centralizer ({markedZ d.flag.module} : Set G))
    (F : BinaryField) :
    (∀ a : Tv (T : Subgroup G) (markedV d.flag.module),
      (∃ g : G, (a : G) = MulAut.conj g (markedZ d.flag.module)) →
      (checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).rangeRestrict a ∈
        center (checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).range →
      ¬ K ≤ centralizer ({(a : G)} : Set G)) ∧
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃*
      PSL(2, F.Carrier)) ∧
    (1 < F.degree →
      ¬ (Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃*
        SL(3, F.Carrier)) ∨
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃*
        Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) ∨
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃*
        Atlas.G2.Model F.Carrier))) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩
  have hzOmega := markedZ_mem_Tv_omega d
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hidx := d.flag_centralizer_index
  have hzGlobal := d.flag.z_central
  have hvT := d.V_le_T (map_mem d.flag.module (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))
  have hv2 : markedV d.flag.module ^ 2 = 1 := by
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [←map_pow]
    have he : (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1 := by decide +kernel
    rw [he,map_one]
  have hv : orderOf (markedV d.flag.module) = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hv2,markedV_ne_one d.flag.module⟩
  have h14 := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have h15 : ∀ (J : Subgroup G)
      (hJ : J ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)),
      let := wk_elementary J L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
        hJ.1.1 hSylow hzOmega hf
      ExcludesAlternatingFiveSeed J L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz := by
    intro J hJ
    exact alternating_seed_excluded_original_source d V₃ earlier standing.qtke hm
      standing.counterexample hfusion hform hfailure J hJ hL hz
  have h16 : ∀ J ∈ Chapter1.LIn (Gv (markedV d.flag.module))
      (Tv (T : Subgroup G) (markedV d.flag.module)),
      Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (J : Set G) →
      ¬ J ≤ centralizer ({markedZ d.flag.module} : Set G) →
      CharacteristicNormalizerObstruction (Tv (T : Subgroup G) (markedV d.flag.module)) J := by
    intro J hJ hn hmove
    exact (component_control_of_replacement_source T L standing h1332 h63
      (markedZ d.flag.module) (markedV d.flag.module) hzGlobal hvT
      (markedV_ne_one d.flag.module) hv2 hSylow hidx hf J hJ hn hmove).2.1
  have h1324 : ChapterB.baumann (T : Subgroup G) ≤
      Tv (T : Subgroup G) (markedV d.flag.module) :=
    baumann_le_Tv_of_alternatives T V V₂ (markedV d.flag.module)
      (map_mem d.flag.module _) d.flag.vector_mem earlier.baumann_alternatives
  have hBV : Mv (normalizer (L : Set G)) (markedV d.flag.module) ≤ normalizer (V : Set G) := by
    rw [c.reductions.local_centralizer]
    exact inf_le_left
  have hW := WK_mem_reducedFamily_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK.1.1
  let D := d.sourceOnFlag
  have hlocal := D.local_residual_le (normalizer (L : Set G)) L.le_normalizer hBV
  have hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        ∀ B : Subgroup X, B.IsCComponent → Chapter1.Section02.A36Conclusion B :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  exact source_noncentrality_and_field_exclusions_of_direct_source D (normalizer (L : Set G))
    hv hL hz hSylow hzOmega hf h14 h15 h16 h1324 earlier.baumann_normalizer
    earlier.module_normalizer hBV hlocal standing h63 hidx hzGlobal K hK hW hA36 F
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
