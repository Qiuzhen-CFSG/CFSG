module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitCoordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitModels
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentPair

/-!
# The complete product alternatives on the original orbit module

The moving component and its conjugate remain distinct ordinary components
inside the original offender subgroup. Apply the corrected B.5 classification
to that same representation. The quasisimple, solvable and outer A₆–C₃
branches are excluded by the actual pair. The remaining two product rows
retain their literal actors, fixed quotient, summands and intertwiners.

This precedes the cubic-diagonal selection of the paired natural row in
13.6.14. No additional classifier, field model, or module decomposition is
assumed in the original-source application.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6, printed p.105; 13.6.14, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every representation field in the two surviving B.5 product rows is
retained on the actual original offender restriction. -/
theorem orbit_product_alternatives_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    let ρ := wkRepresentation K L T z v hL hz
    let σ := ρ.comp (offenderSubgroup ρ).subtype
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  let ρ := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup ρ
  have hlocal := hG.involution_centralizer_sqtk hv
  obtain ⟨t, ht, htN, hp, _, _⟩ :=
    exists_plus_pair_coordinates_source K L T z v hlocal hL hz hSylow hK hn
  let A := plusImage K L T z v hL hz K
  let B := plusImage K L T z v hL hz (K.conjBy t)
  let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
  have hAB : B = A.conjBy (plusMk K L T z v hL hz tA) :=
    plusImage_conjBy_source K L T K z v hL hz (K_le_plusActor K L T v) tA
  have hA : IsComponent (Gplus K L T z v hL hz) A :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩
  have hB : IsComponent (Gplus K L T z v hL hz) B :=
    hAB.symm ▸ hA.map_conj (plusMk K L T z v hL hz tA)
  have hzT := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hzOmega).1
  have hOI := orbit_plus_le_offenders_source K L T z v hL hz hzT hSylow hK
  have hAI : A ≤ I := (map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans hOI
  have hBI : B ≤ I := (map_mono (comap_mono (le_sup_right.trans hp.ge))).trans hOI
  have hne : A.subgroupOf I ≠ B.subgroupOf I := by
    intro he
    have hh := congrArg (map I.subtype) he
    rw [map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI] at hh
    exact plusImage_pair_ne_source K L T z v hlocal hL hz hK hn t ht htN hh
  exact AdequateAlternative.product_rows_of_two_components (ρ.comp I.subtype)
    (orbit_adequateAlternative_source hG K L T z v hv hL hz hSylow hzOmega hf hK)
    (hA.subgroupOf hAI) (hB.subgroupOf hBI) hne

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The full original setup supplies the remaining two corrected B.5
representation alternatives, before the residual containment step. -/
theorem orbit_product_alternatives_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    let ρ := wkRepresentation K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
    let σ := ρ.comp (offenderSubgroup ρ).subtype
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact orbit_product_alternatives_source hG K L (T : Subgroup G) _ _
    (marked_orders d.flag.module).2 hL hz
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩ (markedZ_mem_Tv_omega d)
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion) hK hn

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
