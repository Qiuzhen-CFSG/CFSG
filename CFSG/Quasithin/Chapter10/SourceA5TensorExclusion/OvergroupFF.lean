module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.IrreducibleOmegaOrbit
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupComponent

/-!
# The original tensor overgroup has an FF action

The tensor line lies in the reduced normal closure of the Sylow omega center.
The old component moves its original tensor plane, and its Thompson commutator
identity forces the Thompson subgroup to move the reduced closure. Source B.5
then applies to the actual residual component and faithful action quotient.
This is the FF step of Aschbacher–Smith 9.3.7; no symplectic head is assumed.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
variable {H : Type*} [Group H] [Finite H]

theorem source_tensor_overgroup_ff_from_original_commutator
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (P : Sylow 2 H)
    (R : Subgroup H) (hPR : (P : Subgroup H) = R)
    (K B L U A : Subgroup H) [K.Normal]
    (hK : K.IsCComponent) (hKP : K ⊔ R = ⊤)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hP : R ≠ ⊥)
    (hOmega : omegaCenterIn R ≤ U)
    (hAU : A ≤ normalizer (U : Set H))
    (hirr : ∀ N : Subgroup H, N ≤ U → A ≤ normalizer (N : Set H) →
      N = ⊥ ∨ N = U)
    (hmove : ¬ B ≤ centralizer (componentOrbit U L : Set H))
    (hB : B = ⁅B,elementaryAbelianMaxJ R⁆) :
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      U ≤ W ∧ Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) ((K.map (actionMk W)).subgroupOf N)) := by
  let W := omegaOrbit R
  have hr : IsPReduced 2 W := by simpa only [hPR] using omegaOrbit_reduced P hchar
  refine ⟨hr,?_⟩
  let := hr.normal
  let := hr.elementary
  have hUW : U ≤ W := irreducible_le_omegaOrbit R U A
    (hPR ▸ P.isPGroup') hP hOmega hAU hirr
  have hLW : componentOrbit U L ≤ W :=
    iSup_conjugates_le_of_le_normalizer U L W hUW le_normalizer_of_normal
  have hmove' : ¬ B ≤ centralizer (W : Set H) :=
    fun hc => hmove (hc.trans (centralizer_le hLW))
  have hKP' : K ⊔ (P : Subgroup H) = ⊤ := by simpa only [hPR] using hKP
  have hJ : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    simpa only [hPR] using thompson_moves_of_component_commutator R B W hB hmove'
  exact ⟨hUW,quasisimple_source_conclusion_of_thompson_movement hH P K W hK hKP'
    hr.quotient_pCore_eq_bot hJ⟩
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_tensor_overgroup_ff
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H B U A : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hgen : H = (L ⊔ B) ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hout : ¬ H ≤ D.maximalLocal)
    (hB : B ∈ Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hQ : L.pCoreIn 2 ≤ centralizer (componentOrbit U L : Set G))
    (hBU : B ≤ centralizer (U : Set G))
    (hmove : ¬ B ≤ centralizer (componentOrbit U L : Set G))
    (hUH : U ≤ H)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hOmega : omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ U)
    (hAH : A ≤ H) (hAU : A ≤ normalizer (U : Set G))
    (hirr : ∀ N : Subgroup G, N ≤ U → A ≤ normalizer (N : Set G) →
      N = ⊥ ∨ N = U)
    (hcomm : B = ⁅B,elementaryAbelianMaxJ
      ((T : Subgroup G) ⊓ normalizer (L : Set G))⁆) :
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      U.subgroupOf H ≤ W ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 H).map (actionMk W)).subgroupOf N)) := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hLH : L ≤ H := hgen ▸ le_sup_of_le_left le_sup_left
  have hBH : B ≤ H := hgen ▸ le_sup_of_le_left le_sup_right
  have hRH : R ≤ H := hgen ▸ le_sup_right
  obtain ⟨hK,_,_,hprod⟩ := source_a5_tensor_pair_component_product D e hn H B U
    hcore hgen hout hB hQ hBU hmove
  obtain ⟨P,hP⟩ := source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout
  have hPR : (P : Subgroup H) = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRH]
  have hKP : pResidual 2 H ⊔ (P : Subgroup H) = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := hprod g
    exact mul_mem_sup hk (hPR ▸ hr)
  have hneP : (P : Subgroup H) ≠ ⊥ := by
    intro hz
    exact hcore (bot_unique ((pCore_isPGroup.le_sylow_of_normal P).trans_eq hz))
  have hOmega' : omegaCenterIn (P : Subgroup H) ≤ U.subgroupOf H := by
    have hmap : (omegaCenterIn (P : Subgroup H)).map H.subtype = omegaCenterIn R := by
      change (omegaOneCenterAmbient (P : Subgroup H)).map H.subtype = omegaOneCenterAmbient R
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hP]
    intro x hx
    exact hOmega (hmap ▸ mem_map_of_mem H.subtype hx)
  have hAU' : A.subgroupOf H ≤ normalizer (U.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hUH]
    exact comap_mono hAU
  have hirr' : ∀ N : Subgroup H, N ≤ U.subgroupOf H →
      A.subgroupOf H ≤ normalizer (N : Set H) → N = ⊥ ∨ N = U.subgroupOf H := by
    intro N hNU hAN
    have hNU' : N.map H.subtype ≤ U := by
      simpa only [map_subgroupOf_eq_of_le hUH] using map_mono (f := H.subtype) hNU
    have hAN' : A ≤ normalizer (N.map H.subtype : Set G) := by
      rw [←map_subgroupOf_eq_of_le hAH]
      exact (map_mono hAN).trans (le_normalizer_map H.subtype)
    rcases hirr (N.map H.subtype) hNU' hAN' with hz | he
    · exact .inl ((N.map_eq_bot_iff_of_injective H.subtype_injective).mp hz)
    · exact .inr (map_injective H.subtype_injective (he.trans
        (map_subgroupOf_eq_of_le hUH).symm))
  have horbit : (componentOrbit (U.subgroupOf H) (L.subgroupOf H)).map H.subtype =
      componentOrbit U L := by
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hLH]
  have hmove' : ¬ B.subgroupOf H ≤ centralizer
      (componentOrbit (U.subgroupOf H) (L.subgroupOf H) : Set H) := by
    intro hc
    apply hmove
    intro b hb w hw
    obtain ⟨w',hw',rfl⟩ := horbit ▸ hw
    exact congrArg H.subtype (hc (show (⟨b,hBH hb⟩ : H) ∈ B.subgroupOf H from hb) w' hw')
  have hcomm' : B.subgroupOf H = ⁅B.subgroupOf H,elementaryAbelianMaxJ (P : Subgroup H)⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hBH,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
    exact hcomm
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    obtain ⟨M,hM,hHM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hcore
    have hs := D.simpleQTKE.twoLocal_sqtk hM.1
    exact ⟨hs.stronglyQuasithin.of_injective (inclusion hHM) (inclusion_injective hHM),
      hs.isKGroup.of_injective (inclusion hHM) (inclusion_injective hHM)⟩
  have hKPR : pResidual 2 H ⊔ R.subgroupOf H = ⊤ := by simpa only [hPR] using hKP
  have hneR : R.subgroupOf H ≠ ⊥ := by simpa only [hPR] using hneP
  have hOmegaR : omegaCenterIn (R.subgroupOf H) ≤ U.subgroupOf H := by
    simpa only [hPR] using hOmega'
  have hcommR : B.subgroupOf H = ⁅B.subgroupOf H,elementaryAbelianMaxJ (R.subgroupOf H)⁆ := by
    simpa only [hPR] using hcomm'
  exact source_tensor_overgroup_ff_from_original_commutator hH P (R.subgroupOf H) hPR
    (pResidual 2 H) (B.subgroupOf H) (L.subgroupOf H) (U.subgroupOf H) (A.subgroupOf H)
    hK hKPR hchar hneR hOmegaR hAU' hirr' hmove' hcommR
end CFSG.Quasithin.Chapter10
