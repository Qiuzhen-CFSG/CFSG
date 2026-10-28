module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreAlternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionDisplacement
public import Theory.GroupTheory.SubgroupPartitionCounting
-- The same-package support proof split retains its checked cyclic-action index helper.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# Actual source indices for the partner section

If V is outside the partner core, the core alternative puts F in its
center. The two cyclic support actions give |F:C_F(V)|≤4. F cannot
centralize V, since then the characteristic-two normal-chain theorem
would put V in the core. A moving support has fixed group of order four.
Its intersection with the actual section kernel also fixes that support,
because its displacement lies both in the marked plane and in the
original diagonal partner module. Thus the actual image of V on F/Uc
has order at least four. These are literal source indices, with the
section kernel retained rather than assumed to equal C_Mc(F).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original module lies in the partner core, or its actual section
image is large enough for the fixed-index offender inequality. -/
theorem PreparedChosenModule.decomposable_five_core_or_section_indices
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
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let C := centralizer (Uc:Set G)
      let F := conjugateSpanBy E C
      let K := commutatorPreimage Mc F Uc
      V≤Mc.pCoreIn 2 ∨ ((centralizer (V:Set G)).relIndex F≤4 ∧ 4≤K.relIndex V) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc:Set G)
  let Q := Mc.pCoreIn 2
  let F := conjugateSpanBy E C
  let K := commutatorPreimage Mc F Uc
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  change V≤Q ∨ ((centralizer (V:Set G)).relIndex F≤4 ∧ 4≤K.relIndex V)
  by_cases hVQ:V≤Q
  · exact Or.inl hVQ
  right
  have halt := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨hQE,hFQZ,hEF,hmove,_,_⟩ := halt
  have hFQ : F≤Q := hFQZ.trans inf_le_left
  have hFZ : F≤centralizer (Q:Set G) := hFQZ.trans inf_le_right
  obtain ⟨hCMc,hcore,hQT,_,hself,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,_,hFel,_,hMcF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := hFel
  have hQC : Q≤C := by
    change Mc.pCoreIn 2≤centralizer (localModule T Mc:Set G)
    rw [←hcore]
    exact pCoreIn_le 2 _
  have hQT' : Q≤(T:Subgroup G) := by
    change Mc.pCoreIn 2≤(T:Subgroup G)
    rw [←hcore]
    exact hQT
  have hFT : F≤(T:Subgroup G) := hFQ.trans hQT'
  have hFE : F≤centralizer (E:Set G) := hFZ.trans (centralizer_le (hEF.trans hFQ))
  have hFN₁ : F≤normalizer (V₁:Set G) := by
    intro f hf
    exact s.centralizer_le_stabilizer ⟨hFT hf,
      (hFE.trans (centralizer_le (show thompsonPlane T V
        (c.ambientFactor d s.first).space≤E from inf_le_right))) hf⟩
  have hFN₂ : F≤normalizer (V₂:Set G) := fun f hf=>s.stabilizes_second ⟨hFT hf,hFN₁ hf⟩
  have hidx₁ : (centralizer (V₁:Set G)).relIndex F≤2 :=
    elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive F hFT s.first hFN₁
  have hidx₂ : (centralizer (V₂:Set G)).relIndex F≤2 :=
    elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive F hFT s.second hFN₂
  have hCV : centralizer (V:Set G)=centralizer (V₁:Set G)⊓centralizer (V₂:Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (plane_le _)) (centralizer_le (plane_le _))
    · apply le_centralizer_iff.mpr
      rw [←s.complement]
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  have hidx : (centralizer (V:Set G)).relIndex F≤4 := by
    rw [hCV]
    exact relIndex_inf_le.trans (Nat.mul_le_mul hidx₁ hidx₂)
  have hnFV : ¬F≤centralizer (V:Set G) := by
    intro hc
    have hVC : V≤C := V.le_centralizer.trans
      (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))
    have hCQ : C≤normalizer (Q:Set G) := hCMc.trans (Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))
    have hsQ : C⊓centralizer (Q:Set G)≤Q := by
      change centralizer (localModule T Mc:Set G)⊓centralizer (Mc.pCoreIn 2:Set G)≤Mc.pCoreIn 2
      rw [←hcore]
      exact hself
    have hh := le_twoCore_of_relative_chain C Q F V hQC (hFQ.trans hQC) hVC
      hCQ (hCMc.trans hMcF) (isPGroup_pCoreIn 2 Mc) hsQ
      (le_centralizer_iff.mp hc) (hmove.trans hEF)
    exact hVQ (hh.trans_eq hcore)
  obtain ⟨f,hf,hfn⟩ := Set.not_subset.mp hnFV
  have hex : ∃i:d.Index, f∉centralizer (plane V (c.ambientFactor d i).space:Set G) := by
    by_contra hn
    push Not at hn
    apply hfn
    rw [hCV]
    exact ⟨hn s.first,hn s.second⟩
  obtain ⟨i,hfi⟩ := hex
  let Vi := plane V (c.ambientFactor d i).space
  let Zi := thompsonPlane T V (c.ambientFactor d i).space
  obtain ⟨hfix,hdisp⟩ := s.involution_support_displacement_and_fixed
    hM.1.2 h.normalized c d π hp hs hfive f (hFT hf)
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) f hf) (hFN₁ hf) i
  have hfix' : Vi⊓centralizer ({f}:Set G)≤Zi := hfix.resolve_left hfi
  obtain ⟨hd₁,hd₂,_,_,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hdis : Disjoint Uc Zi := by
    rcases s.covers i with hi|hi
    · simpa only [Zi,hi] using hd₁
    · simpa only [Zi,hi] using hd₂
  have hMcU : Mc≤normalizer (Uc:Set G) := le_normalizer_conjugateSpanBy _ _
  have hthin : K⊓Vi≤Zi := by
    intro v hv
    have hfvU : ⁅f,v⁆∈Uc := by
      rw [←commutatorElement_inv]
      exact Uc.inv_mem (commutator_commutatorPreimage_le Mc F Uc hMcU
        (commutator_mem_commutator hv.1 hf))
    have hcomm : ⁅f,v⁆=1 := disjoint_def.mp hdis hfvU (hdisp v hv.2)
    exact hfix' ⟨hv.2,mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm⟩
  have hsmall : Nat.card (K⊓Vi : Subgroup G)≤4 :=
    (card_le_of_le hthin).trans_eq (s.thompson_card i)
  have hcount := relIndex_mul_card_of_le (show K⊓Vi≤Vi from inf_le_right)
  rw [inf_relIndex_right,s.support_card i] at hcount
  have hlarge : 4≤K.relIndex Vi := by nlinarith
  exact ⟨hidx,hlarge.trans (relIndex_le_of_le_right (plane_le _) index_ne_zero_of_finite)⟩

end CFSG.Quasithin.Chapter15.Section01
