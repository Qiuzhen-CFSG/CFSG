module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelIndices
-- Reuse the checked support-action index bound within the same source proof split.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# Strict source indices from independent quintic support reflections

The original V-image is a strong offender on F/Uc outside the core branch.
The preceding index comparison is already strict unless F has four distinct
actions on V. In that case the two support reflection actions are independent:
one can fix either full support while moving the other. The actual kernel
on F/Uc then meets V only in E, since each isolated displacement lies in a
marked plane disjoint from Uc. Its index in V is at least sixteen, while
|F:C_F(V)| is four. No assertion of universal order four for the V-image is
made, and no best-offender quotient transfer is assumed.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem exists_isolated_support_actor (F C₁ C₂ : Subgroup G)
    (hfull : (C₁⊓C₂).relIndex F=4) (hsmall : C₂.relIndex F≤2) :
    ∃f∈F, f∈C₂ ∧ f∉C₁ := by
  have hn : ¬F⊓C₂≤C₁ := by
    intro hh
    have hi := relIndex_le_of_le_left (le_inf hh (show F⊓C₂≤C₂ from inf_le_right))
      (show (F⊓C₂).relIndex F≠0 from index_ne_zero_of_finite)
    rw [inf_relIndex_left,hfull] at hi
    omega
  obtain ⟨f,hf,hnf⟩ := Set.not_subset.mp hn
  exact ⟨f,hf.1,hf.2,hnf⟩

/-- The original V-image has a strict offender index comparison unless
V is already contained in the original partner core. -/
theorem PreparedChosenModule.decomposable_five_core_or_strict_section_indices
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
      V≤Mc.pCoreIn 2 ∨ (centralizer (V:Set G)).relIndex F<K.relIndex V := by
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
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  change V≤Q ∨ (centralizer (V:Set G)).relIndex F<K.relIndex V
  by_cases hVQ:V≤Q
  · exact Or.inl hVQ
  right
  obtain ⟨hupper,hlower⟩ := (h.decomposable_five_core_or_section_indices
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  change (centralizer (V:Set G)).relIndex F≤4 at hupper
  change 4≤K.relIndex V at hlower
  by_cases hsmall:(centralizer (V:Set G)).relIndex F<4
  · exact hsmall.trans_le hlower
  have hfullidx : (centralizer (V:Set G)).relIndex F=4 := by omega
  obtain ⟨_,hFQZ,hEF,_,_,_⟩ := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨_,hcore,hQT,_,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,_,hFel,_,_⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := hFel
  have hFQ : F≤Q := hFQZ.trans inf_le_left
  have hQT' : Q≤(T:Subgroup G) := by
    change Mc.pCoreIn 2≤(T:Subgroup G)
    rw [←hcore]
    exact hQT
  have hFT : F≤(T:Subgroup G) := hFQ.trans hQT'
  have hFE : F≤centralizer (E:Set G) := (hFQZ.trans inf_le_right).trans
    (centralizer_le (hEF.trans hFQ))
  have hFN₁ : F≤normalizer (V₁:Set G) := by
    intro f hf
    exact s.centralizer_le_stabilizer ⟨hFT hf,
      (hFE.trans (centralizer_le (show Z₁≤E from inf_le_right))) hf⟩
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
  obtain ⟨f₁,hf₁,hf₁C,hf₁n⟩ := exists_isolated_support_actor F
    (centralizer (V₁:Set G)) (centralizer (V₂:Set G)) (hCV ▸ hfullidx) hidx₂
  obtain ⟨f₂,hf₂,hf₂C,hf₂n⟩ := exists_isolated_support_actor F
    (centralizer (V₂:Set G)) (centralizer (V₁:Set G))
    (by rw [inf_comm,←hCV]; exact hfullidx) hidx₁
  obtain ⟨hd₁,hd₂,_,_,_⟩ := h.decomposable_five_partner_four_diagonal_displacement
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hMcU : Mc≤normalizer (Uc:Set G) := le_normalizer_conjugateSpanBy _ _
  have hcommU (f:G) (hf:f∈F) (v:G) (hv:v∈K) : ⁅f,v⁆∈Uc := by
    rw [←commutatorElement_inv]
    exact Uc.inv_mem (commutator_commutatorPreimage_le Mc F Uc hMcU
      (commutator_mem_commutator hv hf))
  have hsupport (i:d.Index) (f:G) (hf:f∈F)
      (hfn:f∉centralizer (plane V (c.ambientFactor d i).space:Set G))
      (hdZ:Disjoint Uc (thompsonPlane T V (c.ambientFactor d i).space))
      (v:G) (hv:v∈plane V (c.ambientFactor d i).space) (hcomm:⁅f,v⁆∈Uc) :
      v∈thompsonPlane T V (c.ambientFactor d i).space := by
    obtain ⟨hfix,hdisp⟩ := s.involution_support_displacement_and_fixed
      hM.1.2 h.normalized c d π hp hs hfive f (hFT hf)
      (elemPow_eq_one_of_isElementaryAbelian (p:=2) f hf) (hFN₁ hf) i
    have he:⁅f,v⁆=1 := disjoint_def.mp hdZ hcomm (hdisp v hv)
    exact (hfix.resolve_left hfn) ⟨hv,mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he).symm⟩
  have hthin : K⊓V≤E := by
    obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V₁ V₂
      (disjoint_iff.mpr s.disjoint) ((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _))))
    intro v hv
    obtain ⟨⟨a,b⟩,hab⟩ := e.surjective ⟨v,s.complement.symm ▸ hv.2⟩
    have hab' : (a:G)*(b:G)=v := (he a b).symm.trans (congrArg Subtype.val hab)
    have haZ : (a:G)∈Z₁ := by
      apply hsupport s.first f₁ hf₁ hf₁n hd₁ a a.property
      have hh:=hcommU f₁ hf₁ v hv.1
      rw [←hab',commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (hf₁C b b.property).symm,
        mul_one,mul_inv_cancel_right] at hh
      exact hh
    have hbZ : (b:G)∈Z₂ := by
      apply hsupport s.second f₂ hf₂ hf₂n hd₂ b b.property
      have hab'' : (b:G)*(a:G)=v :=
        ((V.le_centralizer (plane_le _ a.property) b (plane_le _ b.property))).trans hab'
      have hh:=hcommU f₂ hf₂ v hv.1
      rw [←hab'',commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (hf₂C a a.property).symm,
        mul_one,mul_inv_cancel_right] at hh
      exact hh
    rw [←hab']
    change (a:G)*(b:G)∈thompsonFixed T V
    rw [s.thompson_split]
    exact mul_mem_sup haZ hbZ
  have hcV : Nat.card V=256 := by
    rw [←s.complement,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _)))).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr s.disjoint),
      s.support_card,s.support_card]
  have hsmallK : Nat.card (K⊓V : Subgroup G)≤16 := (card_le_of_le hthin).trans_eq s.fixed_card
  have hcount := relIndex_mul_card_of_le (show K⊓V≤V from inf_le_right)
  rw [inf_relIndex_right,hcV] at hcount
  have hlarge : 16≤K.relIndex V := by nlinarith
  exact hfullidx ▸ (lt_of_lt_of_le (by decide : 4<16) hlarge)

end CFSG.Quasithin.Chapter15.Section01
