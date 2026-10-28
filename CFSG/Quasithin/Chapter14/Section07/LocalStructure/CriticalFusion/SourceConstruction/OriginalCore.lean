module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction

/-!
# The original core commutator before recognition

The actual residual belongs to the local component family and contains U
in its two-core. If the core of H centralizes U, full residual movement
puts U in the intrinsic signalizer module. The residual is then faithful.
Consequently every nonfaithful residual has [U,O₂(H)] = V₁: the original
section gives containment, and V₁ has prime order.

For the genuine G₂(2)′ residual, the earlier 14.3.4 faithful classification
excludes faithful membership by the orders of its two actual quotient
models. This supplies the required 14.5.21(2) instance before Data exists.
The earlier classification retains its producer qt-d-1434-source and final
discharge with qt-d-14775-source; no natural-module recognition is assumed.
Source: Aschbacher–Smith14.3.4,14.5.21(2),14.7.53, pp.990,1019,1065.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalCore
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem residual_mem_localFamily
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent) :
    K F ∈ Chapter1.L G (T : Subgroup G) := by
  let := h.chosen.elementary
  change ((K F).subgroupOf (K F ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [← residual_product F]
  refine ⟨hcomponent, ⟨T.subtype (F.invariant 1),
    map_subgroupOf_eq_of_le (F.invariant 1)⟩, ?_⟩
  have hp : F.Vi 1 ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le ((F.le_seed 1).trans h.chosen.le_sylow))
    ((F.le_seed 1).trans ((le_conjugateSpanBy V F.H).trans F.U_le_H)) le_rfl
  intro hz
  have he : F.Vi 1 = ⊥ := bot_unique (hz ▸ hp)
  have hc := F.card 1 (by decide)
  simp [he] at hc

theorem U_le_residual_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) : F.U ≤ (K F).pCoreIn 2 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hUK : F.U ≤ K F := by
    rw [← commutator_U h F]
    exact le_normalizer_iff_commutator_le_right.mp
      (F.U_le_H.trans (le_normalizer_embedded_pResidual 2 F.H))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U) hUK
    ((show K F ≤ F.H from map_subtype_le _).trans (le_normalizer_conjugateSpanBy V F.H))

theorem residual_faithful_of_core_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hz : ⁅F.U,F.H.pCoreIn 2⁆ = ⊥) :
    K F ∈ MainForward.faithfulLocalComponents T := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hUQ := U_le_residual_core h hab
  have hQH : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (show K F ≤ F.H from map_subtype_le _) (le_normalizer_embedded_pResidual 2 F.H)
  have hc : F.U ≤ centralizer (F.H.pCoreIn 2 : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hz
  have hUC : F.U ≤ omegaOneCenterAmbient ((K F).pCoreIn 2) := by
    intro a ha
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUQ ha, elemPow_eq_one_of_isElementaryAbelian a ha,
        fun q hq => mem_centralizer_iff.mp (hc ha) q (hQH hq)⟩
  have hUm : F.U ≤ ChapterA.Section04.intrinsicSignalizerModule (K F) := by
    calc
      F.U = ⁅F.U, K F⁆ := (commutator_U h F).symm
      _ ≤ ⁅omegaOneCenterAmbient ((K F).pCoreIn 2), K F⁆ := commutator_mono hUC le_rfl
      _ = _ := by rw [ChapterA.Section04.intrinsicSignalizerModule,
        ChapterA.Section04.signalizerModule_eq_commutator_omegaCenter, commutator_comm]; rfl
  apply (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff_module T
    (h.source.simpleQTKE.toIsQTKE.evenCharacteristic T)).mpr
  refine ⟨residual_mem_localFamily h hcomponent, ?_⟩
  intro he
  have hpoint : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hp : F.Vi 1 = ⊥ := bot_unique (hpoint.trans (he ▸ hUm))
  have hc := F.card 1 (by decide)
  simp [hp] at hc

theorem core_commutator_eq_point_of_nonfaithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hn : K F ∉ MainForward.faithfulLocalComponents T) :
    ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hle : ⁅F.U,F.H.pCoreIn 2⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact LocalReduction.section_core_commutator_le_point h s
  have hne : ⁅F.U,F.H.pCoreIn 2⁆ ≠ ⊥ :=
    fun hz => hn (residual_faithful_of_core_centralizes h hab hcomponent hz)
  let A := ⁅F.U,F.H.pCoreIn 2⁆
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let : Fact (Nat.card (F.Vi 1)).Prime := ⟨hcard.symm ▸ Nat.prime_two⟩
  have ht : A.subgroupOf (F.Vi 1) = ⊤ := by
    apply (A.subgroupOf (F.Vi 1)).eq_bot_or_eq_top_of_prime_card.resolve_left
    intro he
    apply hne
    have hm := congrArg (fun S : Subgroup (F.Vi 1) => S.map (F.Vi 1).subtype) he
    rwa [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hm
  have hm := congrArg (fun S : Subgroup (F.Vi 1) => S.map (F.Vi 1).subtype) ht
  rwa [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] at hm

theorem g2_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1 := by
  apply core_commutator_eq_point_of_nonfaithful h hab hcomponent
  intro hfaith
  obtain ⟨hl,hf⟩ := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T (K F)).mp hfaith
  have hc : Nat.card ((K F) ⧸ pCore 2 (K F)) = 6048 :=
    (Nat.card_congr eK.toEquiv).trans Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  rcases (faithful (K F) hl hf).1 with hm | hm
  · obtain ⟨e⟩ := hm
    have hh := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh
    omega
  · obtain ⟨e⟩ := hm
    have hh := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
    omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalCore
