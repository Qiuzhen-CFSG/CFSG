module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixFixedModel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixFixedGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixOriginalAction

/-!
# The original A₆ fixed-space comparison before short-block recognition

The original line [V,Lᵥ] has order four and lies in U_K directly from the
seed commutator identity. Its full movement and Sylow invariance therefore
apply to the actual natural quotient U_K/C_U_K(K). The resulting equality
C_U_K(Lᵥ)=C_U_K(K) uses neither shortness nor a whole-two-core identity.

Source: Aschbacher–Smith 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open LinearThree.CentralAction.ModuleAlternatives BinaryRankTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}

theorem six_fixed_eq_of_localConfiguration
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (m : ConjugationQuotientModel K
      (UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)))
    (hf : Function.Surjective m.actor) :
    UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ⊓
        centralizer (Lv L (markedV d.flag.module) : Set G) =
      UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ⊓
        centralizer (K : Set G) := by
  let s := d.flag.module
  let T₀ := Tv (T : Subgroup G) (markedV s)
  have hSylow : Chapter1.IsSylowIn 2 T₀ (Gv (markedV s)) :=
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩
  have hline : ⁅V,Lv L (markedV s)⁆ ≤
      UK K L (T : Subgroup G) (markedZ s) (markedV s) := by
    rw [AlternatingBranches.ExceptionalActors.moved_eq_seed_commutator s]
    exact commutator_mono (le_conjugateSpanBy _ _) hLK
  have hL : T₀ ≤ normalizer (Lv L (markedV s) : Set G) :=
    AlternatingBranches.CoveredSix.Mv_normalizes_Lv hTL
  have hlineN : Lv L (markedV s) ⊔ T₀ ≤
      normalizer ((⁅V,Lv L (markedV s)⁆ : Subgroup G) : Set G) := by
    refine sup_le (normalizer_commutator_ge_right _ _) ?_
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.T_normalizes ht.1),
      mem_normalizer_iff_map_conj_eq.mp (hL ht)]
  let H : Subgroup G := K ⊔ T₀
  obtain ⟨S,hS⟩ := hSylow.restrict (show T₀ ≤ H from le_sup_right)
    (sup_le hK.1.1 inf_le_right)
  have hS' : (S : Subgroup H) = T₀.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le (show T₀ ≤ H from le_sup_right)]
  obtain ⟨P,hP⟩ := SourceActors.exists_source_sylow hn S hS'
  exact six_fixed_eq_of_moving_four m hf P hP hLK
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv (markedV s))) hL hline
    (AlternatingBranches.ExceptionalActors.moved_self_commutator s)
    (AlternatingBranches.CoveredSix.source_commutator_card s) hlineN

/-- The original flag and A₆ plus image supply the fixed-space comparison
on the literal U_K, with no shortness or extra module premise. -/
theorem six_fixed_eq_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (eC : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 6)) :
    UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ⊓
        centralizer (Lv L (markedV d.flag.module) : Set G) =
      UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ⊓
        centralizer (K : Set G) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  obtain ⟨hW,hmoved⟩ := six_actionData_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz eC
  let := hW
  obtain ⟨m⟩ := hmoved
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  let := plusImage_K_normal K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hL hz hK hn
  obtain ⟨a,ha⟩ := six_quotientModel_of_actionData K L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) hL hz hK.1.1 m
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz (.symplectic ⟨eC.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (F := ZMod 2) (by simp)).symm⟩)).1
  exact six_fixed_eq_of_localConfiguration d c hK hn hLK earlier.T_normalizes_L a ha

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
