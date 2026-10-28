module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwapCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreThompson
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Core

/-!
# Support exchange forces the original module into the partner core

A partner-core element exchanging the two original quintic supports gives
full projections of W=V∩Q. Maximum elementary replacement puts W in J(Q),
so the characteristic envelope F centralizes V. The three-step chain
Q/J(Q), J(Q)/F, F then forces V into Q. No size assumption on V(Mc) is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.decomposable_five_partner_core_exchange_forces_module
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
      ∀q∈Mc.pCoreIn 2,
        q∉normalizer (plane V (c.ambientFactor d s.first).space : Set G) →
        V≤Mc.pCoreIn 2 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive q hqQ hqN
  let V := localModule T M
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  let J := elementaryAbelianMaxJ Q
  let F := conjugateSpanBy E C
  let W := V⊓Q
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  obtain ⟨hCMc,hcore,hQT,_,hself,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  obtain ⟨hJE,_,hFA,_,_,hMcF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  have hJQ : J≤Q := sSup_le fun _ hA => hA.1
  have hFJ : F≤J := by
    intro f hf
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).1
  have hFC : F≤centralizer (J:Set G) := by
    intro f hf
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).2.2
  have hVC : V≤C := V.le_centralizer.trans (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))
  have hCQ : C≤normalizer (Q:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hVQ : V≤normalizer (Q:Set G) := hVC.trans hCQ
  have hQV : Q≤normalizer (V:Set G) := hQT.trans (hM.1.2.trans h.normalized)
  have hmove : ⁅Q,V⁆≤W := le_inf
    (le_normalizer_iff_commutator_le_right.mp hQV)
    (le_normalizer_iff_commutator_le_left.mp hVQ)
  have hqQ' : q∈Q := by
    change q∈(centralizer (localModule T Mc : Set G)).pCoreIn 2
    rw [hcore]
    exact hqQ
  obtain ⟨hq₁,hq₂⟩ := s.exchanges q (hQT hqQ') hqN
  have hr : primeRank 2 (internalActionImage M V h.normalized)≤2 :=
    source_decomposable_action_twoRank hG T hM U c d hd π hp hs hdec
  have hact (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups Q) :
      A≤normalizer (V₁:Set G) ∧ A≤normalizer (V₂:Set G) ∧
      (centralizer (V:Set G)).relIndex A≤4 ∧
      (¬A≤centralizer (V:Set G) →
        4≤(centralizer (A:Set G)).relIndex V₁ ∨
        4≤(centralizer (A:Set G)).relIndex V₂) := by
    let : IsElementaryAbelian 2 A := hA.2.1
    have hAJ : A≤J := le_sSup hA
    have hAT : A≤(T:Subgroup G) := hA.1.trans hQT
    have hAM : A≤M := hAT.trans hM.1.2
    have hAN : A≤normalizer (V₁:Set G) := by
      intro a ha
      exact s.centralizer_le_stabilizer ⟨hAT ha,
        (hAJ.trans hJE |>.trans (centralizer_le (show thompsonPlane T V
          (c.ambientFactor d s.first).space≤E from inf_le_right))) ha⟩
    have hAN₂ : A≤normalizer (V₂:Set G) := fun a ha => s.stabilizes_second ⟨hAT ha,hAN ha⟩
    have hi : (centralizer (V:Set G)).relIndex A≤4 := by
      let f := (actionHom M V h.normalized).rangeRestrict
      let : IsElementaryAbelian 2 (A.subgroupOf M) := IsElementaryAbelian.subgroupOf hAM
      have hB : IsElementaryAbelian 2 ((A.subgroupOf M).map f) := IsElementaryAbelian.map f
      have hh := (primeRank_le_iff_elementary_card_le (internalActionImage M V h.normalized)).mp hr
        ((A.subgroupOf M).map f) hB
      have he : Nat.card ((A.subgroupOf M).map f)=(centralizer (V:Set G)).relIndex A := by
        rw [←relIndex_ker,MonoidHom.ker_rangeRestrict,actionHom_ker,relIndex_subgroupOf hAM]
      calc
        _ = Nat.card ((A.subgroupOf M).map f) := he.symm
        _ ≤ 2^2 := hh
        _ = 4 := rfl
    refine ⟨hAN,hAN₂,hi,?_⟩
    intro hn
    obtain ⟨a,ha,hac⟩ := Set.not_subset.mp hn
    have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha
    have hlo (k:d.Index) (hnk:a∉centralizer (plane V (c.ambientFactor d k).space:Set G)) :
        4≤(centralizer (A:Set G)).relIndex (plane V (c.ambientFactor d k).space) := by
      let Vi := plane V (c.ambientFactor d k).space
      let Zi := thompsonPlane T V (c.ambientFactor d k).space
      have hf := (s.involution_support_displacement_and_fixed hM.1.2 h.normalized c d π hp hs
        hfive a (hAT ha) ha2 (hAN ha) k).1.resolve_left hnk
      have hfix : Vi⊓centralizer (A:Set G)≤Zi :=
        (inf_le_inf_left Vi (centralizer_le (Set.singleton_subset_iff.mpr ha))).trans hf
      have hc : Nat.card (Vi⊓centralizer (A:Set G) : Subgroup G)≤4 :=
        (card_le_of_le hfix).trans_eq (s.thompson_card k)
      have he : Nat.card (Vi⊓centralizer (A:Set G) : Subgroup G)*
          (centralizer (A:Set G)).relIndex Vi=16 := by
        rw [←s.support_card k]
        simpa only [relIndex_bot_left,inf_relIndex_left] using
          relIndex_mul_relIndex (⊥:Subgroup G) (Vi⊓centralizer (A:Set G)) Vi bot_le inf_le_left
      nlinarith
    by_cases hc₁:a∈centralizer (V₁:Set G)
    · right
      apply hlo s.second
      intro hc₂
      apply hac
      have hh : V≤centralizer ({a}:Set G) := by
        change localModule T M≤_
        rw [←s.complement]
        exact sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hc₁ v hv))
          (fun v hv => mem_centralizer_singleton_iff.mpr (hc₂ v hv))
      intro v hv
      exact mem_centralizer_singleton_iff.mp (hh hv)
    · exact Or.inl (hlo s.first hc₁)
  obtain ⟨hWJ,hFV⟩ := maxJ_envelope_centralizes_of_exchanged_supports
    Q V W V₁ V₂ F inf_le_left inf_le_right s.complement (disjoint_iff.mpr s.disjoint)
    hFJ hFC hact q hq₁ hq₂ (fun v hv => hmove (commutator_mem_commutator hqQ' hv))
  have hJV : ⁅J,V⁆≤E :=
    (commutator_mono (le_inf (hJQ.trans hQT) hJE) le_rfl).trans
      (h.decomposable_five_fixed_centralizer_displacement
        hG T hempty hM hmany hJ rfl c d hd s π hp hs hdec hq hfive)
  have hEF : E≤F := le_conjugateSpanBy E C
  have hVcore : V≤Q := le_twoCore_of_relative_three_step_chain C Q J F V
    (pCoreIn_le 2 C) (hJQ.trans (pCoreIn_le 2 C)) (hFJ.trans (hJQ.trans (pCoreIn_le 2 C)))
    hVC hCQ (hCQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
    (hCMc.trans hMcF) (isPGroup_pCoreIn 2 C) hself
    (le_centralizer_iff.mp hFV)
    (by rw [commutator_comm]; exact hJV.trans hEF)
    (by rw [commutator_comm]; exact hmove.trans hWJ)
  exact hVcore.trans_eq hcore

end CFSG.Quasithin.Chapter15.Section01
