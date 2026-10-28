module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSOriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.KnownSimple
public import Theory.SpecificGroups.PSL3Two.PerfectCentralCover

/-!
# Minimal replacement and intrinsic recognition for binary linear three

Choose a local component minimal subject to preserving the original star
image, as in the first sentence of 13.6.22. Original component invariance
and the checked quotient comparison preserve its native plus model and
W_K. The original 13.6.20 theorem then places Lᵥ in this replacement.

If its intrinsic two-core quotient is quasisimple, the literal plus map
is a perfect central covering. The cyclic odd Sylow subgroups of SL₃(2)
and trivial two-core remove its kernel, recovering the intrinsic model
and feeding the original MS-pair construction.

The quasisimplicity of the selected minimal component is still explicit.
The higher-field argument cannot supply it: PSL₃(2) is PSL₂(7), so its rank
comparison does not exclude A.3.6's nonquasisimple natural alternative.
This module proves the replacement and quotient transports, not the full
source intrinsic-recognition step or the C.1.34 classification.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.6.20--22, printed pp.931--932; cyclic-Sylow transfer I.1.2, p.407.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceTransferFields.HigherFieldParabolics.LinearThree
open SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
open SourceTransferFields.RankOneBorel.Replacement
open SourceTransferFields.RankOneBorel.Replacement.MinimalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- For a quasisimple intrinsic quotient, the actual component map has exactly
its two-core as kernel. Transfer on the odd cyclic Sylow subgroups of SL₃(2)
removes the central covering kernel. -/
noncomputable def intrinsicEquivOfQuasisimple
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* BinaryLinearThree.Group)
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group := by
  let f := e.toMonoidHom.comp (componentPlusMap K L T z v hL hz)
  have hf : Function.Surjective f := e.surjective.comp
    (componentPlusMap_surjective K L T z v hL hz)
  have hcore : pCore 2 K ≤ f.ker := by
    have h := subgroupPlusMap_core_le K L T K z v hL hz le_rfl
    have hzero : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
      rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK),
        plus_twoCore_eq_bot_of_reduced K L T z v hL hz hW]
      exact (MonoidHom.ker_eq_bot_iff _).mpr
        (plusImage K L T z v hL hz K).subtype_injective
    rw [hzero] at h
    intro x hx
    change e (componentPlusMap K L T z v hL hz x) = 1
    rw [show componentPlusMap K L T z v hL hz x = 1 from h hx, map_one]
  let q := QuotientGroup.lift (pCore 2 K) f hcore
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  have hk : q.ker ≤ center (K ⧸ pCore 2 K) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    have hm : k ∈ (componentPlusMap K L T z v hL hz).ker := by
      apply e.injective
      exact hx.trans (map_one e).symm
    exact componentPlusMap_ker_central_of_quasisimple_core K L T z v hL hz hK hW
      (mem_map_of_mem _ hm)
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) Matrix.PSL3Two.SL :=
    ⟨q, hq, inferInstance, hk⟩
  exact Matrix.PSL3Two.centralCoverEquiv c (pCore_quotient_pCore_eq_bot 2)

variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Choose exactly as in 13.6.22: minimality is among local components with
the original star image, and the native plus model survives the replacement. -/
theorem exists_minimal_equalStar_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : SourceContainment.RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      SourceContainment.RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* BinaryLinearThree.Group) :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧
      Minimal (fun D => D ∈ Chapter1.LIn
        (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module))
        (Tv (T : Subgroup G) (markedV d.flag.module)) ∧
        starImage (markedZ d.flag.module) (markedV d.flag.module) D =
          starImage (markedZ d.flag.module) (markedV d.flag.module) K) K₀ ∧
      K₀ ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K₀ : Set G) ∧
      WK K₀ L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) =
        WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      Lv L (markedV d.flag.module) ≤ K₀ ∧
      Nonempty (plusImage K₀ L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz K₀ ≃* BinaryLinearThree.Group) := by
  obtain ⟨K₀, hle, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun D : Subgroup G => D ∈ Chapter1.LIn
      (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module))
      (Tv (T : Subgroup G) (markedV d.flag.module)) ∧
      starImage (markedZ d.flag.module) (markedV d.flag.module) D =
        starImage (markedZ d.flag.module) (markedV d.flag.module) K)
    K ⟨⟨le_sup_left, hK.1.2⟩, rfl⟩
  have hlocal : K₀ ∈ Chapter1.LIn (Gv (markedV d.flag.module))
      (Tv (T : Subgroup G) (markedV d.flag.module)) :=
    ⟨hle.trans hK.1.1, hmin.1.1.2⟩
  have hY := mem_Yz_of_starImage_eq L (T : Subgroup G) _ _ hK hlocal hmin.1.2
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hn₀ := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K₀ hY
  let e₀ := modelOfEqualStarImage K₀ K L (T : Subgroup G) _ _ hL hz hK.1.1
    hle hn₀ hn hmin.1.2 e
  have hLV := (SourceContainment.containment_and_noncontainment_original_source d V₃
    earlier standing hm hfusion h1332 h63 hY hL hz
    (SourceContainment.RankTwo.ReducedModel.linear 3 ⟨le_rfl, by decide⟩ ⟨e₀.trans Matrix.PSL3Two.equiv⟩)).1
  exact ⟨K₀, hle, hmin, hY, hn₀,
    WK_eq_of_starImage_eq K₀ K L (T : Subgroup G) _ _ hlocal.1 hK.1.1 hn₀ hn hmin.1.2,
    hLV, ⟨e₀⟩⟩

/-- The quasisimple branch feeds the original MS construction. Every other
source hypothesis, including the reduced-family premise for the literal map,
is supplied by its original producer. -/
theorem intrinsic_model_and_msPair_of_quasisimple_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : SourceContainment.RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      SourceContainment.RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* BinaryLinearThree.Group)
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∧
      CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.LinearThreeMSPair
        KnownSimple.IsKnownSimple K
        (Tv (T : Subgroup G) (markedV d.flag.module)) 1 (ZMod 2) ∧
      MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization.JoinProduct
        K (Tv (T : Subgroup G) (markedV d.flag.module)) := by
  have hW := WK_mem_reducedFamily_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK.1.1
  let f := intrinsicEquivOfQuasisimple K L (T : Subgroup G) _ _ hL hz hK hW e
  exact ⟨⟨f⟩, linearThreeMSPair_original_source d V₃ earlier standing hm hfusion h1332 h63 hK f⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
