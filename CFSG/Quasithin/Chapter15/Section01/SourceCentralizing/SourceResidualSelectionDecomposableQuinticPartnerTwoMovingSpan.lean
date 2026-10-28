module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelSectionIndices
-- Internal source-proof split: reuse the checked literal support displacement
-- surjectivity without changing its frozen owner or exposing it in this API.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelSectionIndices

/-!
# Every moving normal subspace fills the original quintic span

A noncentral elementary actor in an invariant subgroup H of F displaces an
original support onto its marked four-group. Sylow exchange supplies the
other marked four-group. Thus [V,H]=E. Partner normality then puts E in H,
and its literal partner-centralizer conjugates generate all of F inside H.
No reducedness or faithfulness of F is inferred.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- Every actual partner-normal subgroup of F moving V has precisely E as
its displacement, and equals the original full span F. -/
theorem PreparedChosenModule.decomposable_five_moving_normal_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let F := conjugateSpanBy E C
      ∀ H:Subgroup G, H≤F → Mc≤normalizer (H:Set G) →
        ¬H≤centralizer (V:Set G) → ⁅V,H⁆=E ∧ H=F := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  dsimp only
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let F := conjugateSpanBy E C
  intro H hHF hnH hmove
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let R := ⁅V,H⁆
  obtain ⟨hCMc,_,hQT,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,hEA,hFA,heF,_,_⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let Q := C.pCoreIn 2
  let J := elementaryAbelianMaxJ Q
  have hJQ:J≤Q := sSup_le fun _ hA=>hA.1
  have hFJ:F≤J := fun f hf=>((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).1
  have hEJ:E≤J := fun e he=>((mem_omegaOneCenterAmbient_iff _ _).mp (hEA he)).1
  have hFE:F≤centralizer (E:Set G) := by
    intro f hf e he
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).2.2 e (hEJ he)
  have hFT:F≤(T:Subgroup G) := hFJ.trans (hJQ.trans hQT)
  have hHT:H≤(T:Subgroup G) := hHF.trans hFT
  let : IsElementaryAbelian 2 F := heF
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHF
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc:(T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz=>(centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hVMc:V≤Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hHN₁:H≤normalizer (plane V (c.ambientFactor d s.first).space:Set G) := by
    intro f hf
    exact s.centralizer_le_stabilizer ⟨hHT hf,
      (hHF.trans hFE |>.trans (centralizer_le (show Z₁≤E from inf_le_right))) hf⟩
  have hRE:R≤E := by
    change ⁅V,H⁆≤E
    rw [commutator_comm]
    exact (commutator_mono (le_inf hHT (hHF.trans hFE)) le_rfl).trans
      (h.decomposable_five_fixed_centralizer_displacement
        hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive)
  have hRT:(T:Subgroup G)≤normalizer (R:Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (h.normalized (hM.1.2 ht)),
      mem_normalizer_iff_map_conj_eq.mp (hnH (hTMc ht))]
  obtain ⟨f,hf,hfC⟩ := Set.not_subset.mp hmove
  have hex:∃i:d.Index,f∉centralizer (plane V (c.ambientFactor d i).space:Set G) := by
    by_contra hn
    push Not at hn
    apply hfC
    have hvf:V≤centralizer ({f}:Set G) := by
      rw [←s.complement]
      exact sup_le
        (fun v hv=>mem_centralizer_singleton_iff.mpr (hn s.first v hv))
        (fun v hv=>mem_centralizer_singleton_iff.mpr (hn s.second v hv))
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hvf hv)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨hfix,hdisp⟩ := s.involution_support_displacement_and_fixed
    hM.1.2 h.normalized c d π hp hs hfive f (hHT hf)
      (elemPow_eq_one_of_isElementaryAbelian (p:=2) f hf) (hHN₁ hf) i
  let Vi := plane V (c.ambientFactor d i).space
  let Zi := thompsonPlane T V (c.ambientFactor d i).space
  let : IsElementaryAbelian 2 Vi := IsElementaryAbelian.of_le (plane_le _)
  have hZiR:Zi≤R := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := full_support_displacement Vi Zi inf_le_left
      (s.support_card i) (s.thompson_card i) f (hfix.resolve_left hi) hdisp z hz
    change ⁅f,v⁆∈⁅V,H⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hf (plane_le _ hv)
  obtain ⟨t,ht,hout⟩ : ∃t∈(T:Subgroup G),
      t∉normalizer (plane V (c.ambientFactor d s.first).space:Set G) := by
    by_contra! hall
    have he := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at he
    contradiction
  have hexchange := s.thompson_exchanges t ht hout
  have hmapR:R.map (MulAut.conj t).toMonoidHom=R := mem_normalizer_iff_map_conj_eq.mp (hRT ht)
  have hpair:Z₁≤R ∧ Z₂≤R := by
    rcases s.covers i with he | he
    · have h1:Z₁≤R := by simpa only [Zi, Z₁, he] using hZiR
      have h2 := (map_mono h1).trans_eq hmapR
      rw [hexchange.1] at h2
      exact ⟨h1,h2⟩
    · have h2:Z₂≤R := by simpa only [Zi, Z₂, he] using hZiR
      have h1 := (map_mono h2).trans_eq hmapR
      rw [hexchange.2] at h1
      exact ⟨h1,h2⟩
  have hER:E≤R := by
    change thompsonFixed T V≤R
    rw [s.thompson_split]
    exact sup_le hpair.1 hpair.2
  have hEq:R=E := le_antisymm hRE hER
  have hEH:E≤H := hER.trans
    (le_normalizer_iff_commutator_le_right.mp (hVMc.trans hnH))
  exact ⟨hEq,le_antisymm hHF (conjugateSpanBy_le hEH (hCMc.trans hnH))⟩

end CFSG.Quasithin.Chapter15.Section01
