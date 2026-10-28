module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionStrongSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionBestGeometry
public import Theory.Representation.BinaryConjugationSection.DualOffenderIndex
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
-- Reuse the checked support-action index bound within the same source proof split.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# The whole original quintic image is minimal best

The original two-support pairing gives an actual image of rank two or four.
Faithful quadratic displacement into the marked quotient plane bounds every
subgroup rank by twice its fixed codimension. Equality for the whole original
image then gives strictly larger weight than every proper subgroup.
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

/-- The full reflection image forces an original section actor of order at least sixteen. -/
private theorem PreparedChosenModule.core_or_pairing_index_alternative
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
      V≤Mc.pCoreIn 2 ∨ ((centralizer (V:Set G)).relIndex F<4 ∨ 16≤K.relIndex V) := by
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
  change V≤Q ∨ ((centralizer (V:Set G)).relIndex F<4 ∨ 16≤K.relIndex V)
  by_cases hVQ:V≤Q
  · exact Or.inl hVQ
  right
  obtain ⟨hupper,hlower⟩ := (h.decomposable_five_core_or_section_indices
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  change (centralizer (V:Set G)).relIndex F≤4 at hupper
  change 4≤K.relIndex V at hlower
  by_cases hsmall:(centralizer (V:Set G)).relIndex F<4
  · exact Or.inl hsmall
  right
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
  exact hlarge

/-- The original module lies in the partner core, or its actual image is a
minimal best strong offender on the faithful action of the original partner section. -/
theorem PreparedChosenModule.decomposable_five_core_or_section_minimal_best_offender
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
      Nat.card (localModule T Mc) = 4 →
      let Uc := localModule T Mc
      let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
      V ≤ Mc.pCoreIn 2 ∨
        ∃ he : IsElementaryAbelian 2 F,
          letI := he
          ∃ ρ : Representation (ZMod 2) Mc (Additive (F ⧸ Uc.subgroupOf F)),
            Nonempty (BinaryConjugationSection Mc F Uc ρ) ∧
            Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
            (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
              commutatorPreimage Mc F Uc ∧
            Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
              (commutatorPreimage Mc F Uc).relIndex V ∧
            pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
            IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            IsQuadratic (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            Module.finrank (ZMod 2) (subspaceCommutator
              (Representation.BinaryOffender.imageRepresentation ρ) ⊤
              (actionSubgroup ρ (V.subgroupOf Mc))) ≤ 2 ∧
            IsMinimalBestOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            ((rank (actionSubgroup ρ (V.subgroupOf Mc)) = 2 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) = 1) ∨
             (rank (actionSubgroup ρ (V.subgroupOf Mc)) = 4 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) = 2)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  obtain hcore | ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hoff⟩ :=
    h.decomposable_five_core_or_section_strong_offender
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact (hVQ hcore).elim
  right
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hUE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le (hUE.trans inf_le_left))
  have hVMc : V ≤ Mc := hVC.trans (localModule_centralizer_le_partner T Mc hu)
  have hVF : ⁅V,F⁆ ≤ E := by
    rcases h.decomposable_five_partner_core_alternatives
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with hq | hh
    · exact (hVQ hq).elim
    · exact hh.2.2.2.2.1
  have hquad : IsQuadratic σ A := by
    apply dF.quadratic_of_commutator_bounds σ
      (Representation.BinaryOffender.actionHom ρ) V E hVF
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (V.le_centralizer.trans (centralizer_le inf_le_left))).le.trans bot_le
  have hplane : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 2 := by
    have hdim : Module.finrank (ZMod 2) (dF.imageSpace E) = 2 := by
      apply dF.imageSpace_finrank_of_index E (le_conjugateSpanBy E C) 2
      have hm := (Uc.subgroupOf E).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv] at hm
      change Uc.relIndex E * Nat.card Uc = Nat.card E at hm
      rw [hcU,s.fixed_card] at hm
      change Uc.relIndex E = 2 ^ 2
      have hm' : Uc.relIndex E * 4 = 16 := hm
      norm_num only [Nat.reducePow]
      omega
    have hmove : subspaceCommutator σ ⊤ A ≤ dF.imageSpace E := by
      change subspaceCommutator σ ⊤ ((V.subgroupOf Mc).map
        (Representation.BinaryOffender.actionHom ρ)) ≤ _
      rw [←subspaceCommutator_comp_map]
      change subspaceCommutator ρ ⊤ (V.subgroupOf Mc) ≤ _
      have he := dF.imageSpace_commutator V F hVMc le_rfl
      rw [dF.imageSpace_self] at he
      rw [←he]
      exact dF.imageSpace_mono hVF
    exact (Submodule.finrank_mono hmove).trans_eq hdim
  obtain ⟨hupper,hlower⟩ := (h.decomposable_five_core_or_section_indices
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hfixed := dF.fixed_quotient_card_le_centralizer_index σ
    (Representation.BinaryOffender.actionHom ρ) V
  change Nat.card ((Additive (F ⧸ Uc.subgroupOf F)) ⧸ fixedSpace σ A) ≤
    (centralizer (V:Set G)).relIndex F at hfixed
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hfixed
  change 2^fixedCodim σ A ≤ (centralizer (V:Set G)).relIndex F at hfixed
  have htwo : fixedCodim σ A ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (hfixed.trans hupper)
  have hrank : 2≤rank A := by
    have hh : 4≤Nat.card A := by rw [hcard];exact hlower
    rw [hoff.1.card_eq_two_pow_rank] at hh
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hh
  let : IsElementaryAbelian 2 A := hoff.1.2
  have hbound : rank A≤2*fixedCodim σ A :=
    DecomposableQuinticControl.rank_le_twice_fixedCodim_of_moved_plane σ hfaith A A le_rfl hplane
  have hcost : (rank A=2 ∧ fixedCodim σ A=1) ∨
      (rank A=4 ∧ fixedCodim σ A=2) := by
    rcases (h.core_or_pairing_index_alternative
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ with
      hsmall | hlarge
    · have hsmall' : 2^fixedCodim σ A<2^2 := hfixed.trans_lt hsmall
      have hc : fixedCodim σ A<2 :=
        (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hsmall'
      exact Or.inl ⟨by omega,by omega⟩
    · have hh : 16≤Nat.card A := by rw [hcard];exact hlarge
      rw [hoff.1.card_eq_two_pow_rank] at hh
      have hr : 4≤rank A := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hh
      exact Or.inr ⟨by omega,by omega⟩
  exact ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hoff,hquad,hplane,
    DecomposableQuinticControl.minimalBestOffender_of_moved_plane_exact_cost
      σ hfaith A hoff.1 hplane hcost,hcost⟩

end CFSG.Quasithin.Chapter15.Section01
