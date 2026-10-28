module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSeedIntersections
public import Theory.Representation.BinaryConjugationSection.ActionKernel
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
-- Same-subsystem proof split: use the frozen support action index and isolated-actor helpers.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelPairing

/-!
# Strongness of the original actor on a three-dimensional canonical seed

For the actual canonical F/D section with partner module of order two, a
three-dimensional image of E makes D disjoint from each marked support
plane. A moving support gives an original V-image of order at least four.
If F has four distinct actions on V, isolated support reflections instead
force the section kernel in V into E, giving index at least sixteen.
These bounds make the fixed-section comparison strict. The action supplied
by the caller, its original V-image, and its full section kernel are kept.
No quotient inheritance of an offender is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- Outside the original partner core, every supplied literal canonical
section with three-dimensional seed retains the original V-image as a
strong offender, with a strict comparison against its actual kernel. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_strong
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
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let K := commutatorPreimage Mc F D
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          (centralizer (V : Set G)).relIndex F < K.relIndex V ∧
            IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := Mc.pCoreIn 2
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  by_cases hVQ : V ≤ Q
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hdim
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  obtain ⟨_,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
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
  obtain ⟨_,_,_,himages⟩ := (h.decomposable_five_partner_two_seed_intersections
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  obtain ⟨_,hdimeq,_,hrows⟩ := himages ρ dF
  have hdim₁ : Module.finrank (ZMod 2) (dF.imageSpace Z₁) = 2 := by
    rcases hrows with hthree | htwo | hone
    · exact hthree.2.2.1
    · have hh := htwo.2
      omega
    · have hh := hone.2.1
      omega
  have hdim₂ : Module.finrank (ZMod 2) (dF.imageSpace Z₂) = 2 := hdimeq.symm.trans hdim₁
  have hdis (i : d.Index) : Disjoint D (thompsonPlane T V (c.ambientFactor d i).space) := by
    let Zi := thompsonPlane T V (c.ambientFactor d i).space
    have hdimZi : Module.finrank (ZMod 2) (dF.imageSpace Zi) = 2 := by
      rcases s.covers i with hi | hi
      · change Module.finrank (ZMod 2) (dF.imageSpace (thompsonPlane T V (c.ambientFactor d i).space)) = 2
        rw [hi]
        exact hdim₁
      · change Module.finrank (ZMod 2) (dF.imageSpace (thompsonPlane T V (c.ambientFactor d i).space)) = 2
        rw [hi]
        exact hdim₂
    have hcZi := dF.imageSpace_card_eq_relIndex Zi
      ((show Zi ≤ E from inf_le_right).trans hEF)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdimZi] at hcZi
    have hcount := relIndex_mul_card_of_le (show D ⊓ Zi ≤ Zi from inf_le_right)
    rw [inf_relIndex_right, ←hcZi, s.thompson_card i] at hcount
    apply disjoint_iff.mpr
    apply Subgroup.card_eq_one.mp
    change Nat.card (D ⊓ Zi : Subgroup G) = 1
    have hcount' : 4 * Nat.card (D ⊓ Zi : Subgroup G) = 4 := by
      simpa only [Nat.reducePow] using hcount
    omega
  have hcommD (f : G) (hf : f ∈ F) (v : G) (hv : v ∈ K) : ⁅f,v⁆ ∈ D := by
    rw [←commutatorElement_inv]
    exact D.inv_mem (commutator_commutatorPreimage_le Mc F D hnD
      (commutator_mem_commutator hv hf))
  have hsupport (i : d.Index) (f : G) (hf : f ∈ F)
      (hfn : f ∉ centralizer (plane V (c.ambientFactor d i).space : Set G))
      (v : G) (hv : v ∈ plane V (c.ambientFactor d i).space) (hcomm : ⁅f,v⁆ ∈ D) :
      v ∈ thompsonPlane T V (c.ambientFactor d i).space := by
    obtain ⟨hfix,hdisp⟩ := s.involution_support_displacement_and_fixed
      hM.1.2 h.normalized c d π hp hs hfive f (hFT hf)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf) (hFN₁ hf) i
    have he : ⁅f,v⁆ = 1 := disjoint_def.mp (hdis i) hcomm (hdisp v hv)
    exact (hfix.resolve_left hfn) ⟨hv,mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp he).symm⟩
  have hlower : 4 ≤ K.relIndex V := by
    obtain ⟨f,hf,hfn⟩ := Set.not_subset.mp hnFV
    have hex : ∃ i : d.Index, f ∉ centralizer (plane V (c.ambientFactor d i).space : Set G) := by
      by_contra hn
      push Not at hn
      apply hfn
      rw [hCV]
      exact ⟨hn s.first,hn s.second⟩
    obtain ⟨i,hfi⟩ := hex
    let Vi := plane V (c.ambientFactor d i).space
    let Zi := thompsonPlane T V (c.ambientFactor d i).space
    have hthin : K ⊓ Vi ≤ Zi := fun v hv => hsupport i f hf hfi v hv.2 (hcommD f hf v hv.1)
    have hsmall : Nat.card (K ⊓ Vi : Subgroup G) ≤ 4 :=
      (card_le_of_le hthin).trans_eq (s.thompson_card i)
    have hcount := relIndex_mul_card_of_le (show K ⊓ Vi ≤ Vi from inf_le_right)
    rw [inf_relIndex_right, s.support_card i] at hcount
    have hlarge : 4 ≤ K.relIndex Vi := by nlinarith
    exact hlarge.trans (relIndex_le_of_le_right (plane_le _) index_ne_zero_of_finite)
  have hstrict : (centralizer (V : Set G)).relIndex F < K.relIndex V := by
    by_cases hsmall : (centralizer (V : Set G)).relIndex F < 4
    · exact hsmall.trans_le hlower
    have hfullidx : (centralizer (V : Set G)).relIndex F = 4 := by omega
    obtain ⟨f₁,hf₁,hf₁C,hf₁n⟩ := exists_isolated_support_actor F
      (centralizer (V₁:Set G)) (centralizer (V₂:Set G)) (hCV ▸ hfullidx) hidx₂
    obtain ⟨f₂,hf₂,hf₂C,hf₂n⟩ := exists_isolated_support_actor F
      (centralizer (V₂:Set G)) (centralizer (V₁:Set G))
      (by rw [inf_comm,←hCV]; exact hfullidx) hidx₁
    have hthin : K⊓V≤E := by
      obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V₁ V₂
        (disjoint_iff.mpr s.disjoint) ((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _))))
      intro v hv
      obtain ⟨⟨a,b⟩,hab⟩ := e.surjective ⟨v,s.complement.symm ▸ hv.2⟩
      have hab' : (a:G)*(b:G)=v := (he a b).symm.trans (congrArg Subtype.val hab)
      have haZ : (a:G)∈Z₁ := by
        apply hsupport s.first f₁ hf₁ hf₁n a a.property
        have hh:=hcommD f₁ hf₁ v hv.1
        rw [←hab',commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_mul_comm.mpr (hf₁C b b.property).symm,
          mul_one,mul_inv_cancel_right] at hh
        exact hh
      have hbZ : (b:G)∈Z₂ := by
        apply hsupport s.second f₂ hf₂ hf₂n b b.property
        have hab'' : (b:G)*(a:G)=v :=
          ((V.le_centralizer (plane_le _ a.property) b (plane_le _ b.property))).trans hab'
        have hh:=hcommD f₂ hf₂ v hv.1
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
  refine ⟨hstrict, ?_⟩
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hk : (Representation.BinaryOffender.actionHom ρ).ker = ρ.ker := by
    ext a
    change Representation.BinaryOffender.actionHom ρ a = 1 ↔ ρ a = 1
    rw [actionHom_eq_one_iff]
    constructor
    · exact fun he => LinearMap.ext he
    · exact fun he v => congrArg (fun f : Module.End (ZMod 2) W => f v) he
  have hkm : (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype = K := by
    rw [hk]
    exact dF.action_kernel_map hnD
  have hc : Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) = K.relIndex V := by
    change Nat.card ((V.subgroupOf Mc).map (Representation.BinaryOffender.actionHom ρ)) = _
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective (Representation.BinaryOffender.actionHom ρ).ker
      (V.subgroupOf Mc) Mc.subtype_injective
    rw [hkm, map_subgroupOf_eq_of_le hVMc] at he
    exact he.symm
  let : IsElementaryAbelian 2 (V.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hVMc
  have he : IsElementaryTwo (actionSubgroup ρ (V.subgroupOf Mc)) := by
    refine ⟨?_, IsElementaryAbelian.map (Representation.BinaryOffender.actionHom ρ)⟩
    intro hz
    rw [hz] at hc
    simp only [Subgroup.card_bot] at hc
    omega
  refine ⟨he, ?_⟩
  have hb := dF.fixed_quotient_card_le_centralizer_index
    (Representation.BinaryOffender.imageRepresentation ρ)
    (Representation.BinaryOffender.actionHom ρ) V
  have hs : Nat.card (W ⧸ fixedSpace (Representation.BinaryOffender.imageRepresentation ρ)
      (actionSubgroup ρ (V.subgroupOf Mc))) < Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) := by
    rw [hc]
    exact hb.trans_lt hstrict
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    he.card_eq_two_pow_rank] at hs
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hs

end CFSG.Quasithin.Chapter15.Section01
