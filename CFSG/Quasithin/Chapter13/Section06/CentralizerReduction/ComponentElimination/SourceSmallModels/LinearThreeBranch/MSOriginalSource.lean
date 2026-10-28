module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.OriginalSource

/-!
# The original binary linear-three MS pair

The original 13.6.6 characteristic-two result restricts to the Sylow
overgroup K Tᵥ. Local component membership makes Tᵥ itself a proper
odd-index two-core witness for (MS2)(a). The original 13.6.16 strict
characteristic-normalizer theorem supplies (MS3), and 13.6.14 supplies
the actual set product in (MS1).

We retain that product beside the older `LinearThreeMSPair` record, whose
fields only describe the join. The MS93 consumer receives a complete
`BinaryMS.Input` on the literal join and preserves the given marking of
K/O₂(K). The source hypothesis identifying that quotient remains explicit;
this does not classify the five C.1.34 module alternatives.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
C.1.31, printed p.135, and 13.6.6,14--16,22, printed pp.926--932.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceTransferFields.HigherFieldParabolics
open MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem msOddIndex_of_local {K R : Subgroup G}
    (hK : K ∈ Chapter1.L G R) : MSOddIndex K R := by
  have hS := hK.2.1
  have hp := (Chapter1.isSylowIn_iff.mp hS).1
  have hproper : R < K ⊔ R := by
    apply lt_of_le_not_ge le_sup_right
    intro hle
    have hKR : K ≤ R := le_sup_left.trans hle
    have hk : IsPGroup 2 (K.subgroupOf (K ⊔ R)) :=
      (hp.to_le hKR).comap_subtype
    let := hk.isNilpotent
    exact hK.1.not_isSolvable inferInstance
  refine ⟨R, hproper, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := hS
    have he : R.subgroupOf (K ⊔ R) = (P : Subgroup (K ⊔ R : Subgroup G)) := by
      calc
        R.subgroupOf (K ⊔ R) = ((P : Subgroup (K ⊔ R : Subgroup G)).map
            (K ⊔ R).subtype).subgroupOf (K ⊔ R) := congrArg (fun A => A.subgroupOf (K ⊔ R)) hP.symm
        _ = _ := comap_map_eq_self_of_injective (K ⊔ R).subtype_injective _
    rw [he]
    exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index he.two_dvd)
  · have hcore : pCore 2 R = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
    rw [pCoreIn, hcore, ← MonoidHom.range_eq_map, range_subtype]

/-- The source local hypotheses construct every MS clause and the literal
product required by (MS1), beyond the join recorded by the legacy interface. -/
theorem linearThreeMSPair_of_local_source
    {κ : GroupClass.{u}} {K L T : Subgroup G} {z v : G}
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hsq : IsSQTK κ (Gv v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (h16 : CharacteristicNormalizerObstruction (Tv T v) K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2) ∧ JoinProduct K (Tv T v) := by
  let H := K ⊔ Tv T v
  have hH : H ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hsqH : IsSQTK κ H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hH)).mp (hsq.subgroup (H.subgroupOf (Gv v)))
  obtain ⟨S, hS⟩ := hSylow
  have hSH : (S : Subgroup (Gv v)).map (Gv v).subtype ≤ H := hS ▸ le_sup_right
  have hchar : HasCharacteristicTwo (Gv v) := by
    change centralizer (pCore 2 (Gv v) : Set (Gv v)) ≤ pCore 2 (Gv v)
    rw [← hf]
    exact centralizer_generalizedFitting_le (Gv v)
  have hc : HasCharacteristicTwo (H.subgroupOf (Gv v)) :=
    centralizer_pCore_le_of_sylow_le S (H.subgroupOf (Gv v))
      (map_le_iff_le_comap.mp hSH) hchar
  have hfH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (hc.of_equiv (subgroupOfEquivOfLe hH))
  refine ⟨{
    positive := by decide
    field_card := by simp
    model := ⟨e⟩
    sqtk := hsqH
    fitting := hfH
    component := ⟨le_sup_left, hK.1.2.1⟩
    radical := Or.inl (msOddIndex_of_local hK.1.2)
    characteristic := ?_ }, joinProduct_of_normalizes hn⟩
  intro C hC hnC
  by_contra hne
  exact characteristic_exclusion _ _ h16 C hC hne hnC

variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Original 13.6.6 and 13.6.14--16 construct the genuine MS pair used in
13.6.22, including its full product clause. The model is on K/O₂(K). -/
theorem linearThreeMSPair_original_source
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
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    LinearThreeMSPair KnownSimple.IsKnownSimple K
      (Tv (T : Subgroup G) (markedV d.flag.module)) 1 (ZMod 2) ∧
    JoinProduct K (Tv (T : Subgroup G) (markedV d.flag.module)) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hf := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hvT := d.V_le_T (map_mem d.flag.module
    (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))
  have hv := (marked_orders d.flag.module).2
  have hv2 : markedV d.flag.module ^ 2 = 1 := by
    rw [← hv]
    exact pow_orderOf_eq_one _
  have hmove : ¬ K ≤ centralizer ({markedZ d.flag.module} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff _ _ K hK.1.1).mpr hc)
  have h16 := (component_control_of_replacement_source T L standing h1332 h63
    (markedZ d.flag.module) (markedV d.flag.module) d.flag.z_central hvT
    (markedV_ne_one d.flag.module) hv2 hSylow d.flag_centralizer_index hf K hK.1 hn
    hmove).2.1
  exact linearThreeMSPair_of_local_source hK hn hSylow
    (standing.qtke.involution_centralizer_sqtk hv) hf h16 e

/-- The actual MS93 input on the join, with all original MS hypotheses
constructed and the precise two-core quotient marking retained. -/
theorem binaryMSInput_original_source
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
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ∃ i : BinaryMS.Input KnownSimple.IsKnownSimple
        (K.subgroupOf (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module)))
        ((Tv (T : Subgroup G) (markedV d.flag.module)).subgroupOf
          (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module))),
      i.quotientEquiv = joinQuotientEquiv e := by
  have h := linearThreeMSPair_original_source d V₃ earlier standing hm hfusion h1332 h63 hK e
  exact ⟨inputOfProductOddIndex h.1 e h.2 (msOddIndex_of_local hK.1.2), rfl⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
