module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitNativePair
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairMarkedContradiction
/-!
# Original 13.6.14: invariance of every selected component

A component not normalized by T_v has an orbit of length two. The source
rank descent places L_v in that orbit in the plus quotient. The adequate B.5
classification then produces the actual exchanged natural SL_2 pair. Its
marked seed and Baumann image give a paired Borel normalizing V, whose odd
square divisor contradicts the original five-point normalizer action.

All intermediate placement, model, action, seed-coordinate and Baumann
conclusions are constructed from the earlier source setup. No invariance
premise or alternative marker is retained.
Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open A5Module ComponentReduction InitialSieve
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem component_invariant_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) :
    Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G) := by
  by_contra hn
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  have hL := markedTv_normalizes_Lv d V₃ earlier
  have hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (markedZ_mem_Tv_omega d)).2.2 t ht)
  have hpair := orbit_native_pair_original_source d V₃ earlier hG hm hcounter hfusion K hK hn hL hz
  dsimp only at hpair
  obtain ⟨a,F,hF,_,c,hI,t,ht,hex⟩ := hpair
  exact pair_marked_contradiction_original_source d V₃ earlier hG hcounter hfusion K hK hn hL hz
    (plusLv_le_Kminus_original_source d V₃ earlier hG hm hcounter hfusion K hK hn hL hz)
    a F hF c hI t ht hex

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
