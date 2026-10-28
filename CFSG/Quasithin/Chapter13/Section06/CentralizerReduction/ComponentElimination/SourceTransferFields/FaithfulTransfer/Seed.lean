module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.Signalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson

/-!
# Nontriviality of the selected component's intrinsic module

The source seed z lies in the omega-center of Tᵥ. The earlier equality
F*(Gᵥ) = O₂(Gᵥ) places Uᵥ, and hence z, in Ω₁(Z(O₂(Gᵥ))). The core
of Gᵥ lies in O₂(KTᵥ), while the latter core lies in the Sylow subgroup
Tᵥ. Thus z also lies in Ω₁(Z(O₂(KTᵥ))). Membership in Y_z and the
13.6.14 invariance of K show that K moves z. A.4.9 in KTᵥ now makes
V(K) nontrivial, supplying the input of the first signalizer transfer.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
13.6.6 and 13.6.14–17, printed pp.926–930; A.4.9, printed p.60.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields
open ChapterA.Section04 Chapter1.Section02.Adequate ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- Derive V(K) ≠ 1 using the actual Y_z member, its invariant orbit,
and the earlier characteristic-two and central-seed data. -/
theorem intrinsic_module_ne_bot_of_source_seed
    (T L K : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hTK : Tv T v ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    intrinsicSignalizerModule K ≠ ⊥ := by
  have hnc : ¬ K ≤ centralizer ({z} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L T z v hK hTK).1.2
      ((starPreimage_starImage_centralizes_seed_iff z v K hK.1.1).mpr hc)
  let H := K ⊔ Tv T v
  have hHG : H ≤ Gv v := sup_le hK.1.1 inf_le_right
  obtain ⟨P, hP⟩ := hSylow
  have hQT : Qv v ≤ Tv T v := hP ▸ pCoreIn_le_sylow (Gv v) P
  have hQH : Qv v ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 (Gv v)) (hQT.trans le_sup_right)
    (hHG.trans ((Gv v).le_normalizer.trans (normalizer_le_normalizer_intrinsicCore _)))
  obtain ⟨S, hS⟩ := hK.1.2.2.1
  have hHT : H.pCoreIn 2 ≤ Tv T v := hS ▸ pCoreIn_le_sylow H S
  have hzQ := (mem_omegaOneCenterAmbient_iff _ _).mp
    (Uv_le_coreOmega T z v ⟨P, hP⟩ hz hf (z_mem_Uv z v))
  obtain ⟨_, hz2, hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzH : z ∈ omegaOneCenterAmbient (H.pCoreIn 2) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hQH hzQ.1, hz2, fun x hx => hzc x (hHT hx)⟩
  apply (intrinsic_ne_bot_iff_core_module_ne_bot K H le_sup_left
    hK.1.2.1.subnormal (mem_L_isPPerfect hK.1.2)).mpr
  intro he
  have hc := commutator_eq_bot_iff_le_centralizer.mp
    ((signalizerModule_eq_commutator_omegaCenter K (H.pCoreIn 2)).symm.trans he)
  apply hnc
  intro k hk
  exact mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp (hc hk) z hzH).symm)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields

end
