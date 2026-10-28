module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoDisjointStrong
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionBestGeometry
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# The two original support actors on the canonical section

When D misses the two marked planes, each original support has a faithful
image of rank two and fixed codimension one. Actual Sylow exchange ensures
that F moves both supports. The original reflection calculation gives the
kernel lower bound and the fixed-codimension upper bound; faithful
displacement into the image plane makes both bounds exact. Thus each
unchanged support image is a minimal best strong offender, and its moved
space is exactly its original marked plane image.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Each literal support image is a strong minimal plane offender on the
same canonical section when the denominator misses the marked planes. -/
theorem PreparedChosenModule.decomposable_five_partner_two_support_actors
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
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          D ⊓ Z₁ = ⊥ →
          ∀ i : d.Index,
            let Ai := actionSubgroup ρ ((plane V (c.ambientFactor d i).space).subgroupOf Mc)
            let Pi := dF.imageSpace (thompsonPlane T V (c.ambientFactor d i).space)
            let σ := Representation.BinaryOffender.imageRepresentation ρ
            rank Ai = 2 ∧ fixedCodim σ Ai = 1 ∧
              IsMinimalBestOffender σ Ai ∧ IsStrongOffender σ Ai ∧
              subspaceCommutator σ ⊤ Ai = Pi := by
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
  intro W _ _ ρ dF hDZ₁
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
  obtain ⟨hcards,_,_,_⟩ := (h.decomposable_five_partner_two_seed_intersections.{u,0}
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hDZ₂ : D ⊓ Z₂ = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [←hcards,hDZ₁,Subgroup.card_bot]
  have hdis (i : d.Index) : Disjoint D (thompsonPlane T V (c.ambientFactor d i).space) := by
    rcases s.covers i with hi | hi
    · rw [hi]
      exact disjoint_iff.mpr hDZ₁
    · rw [hi]
      exact disjoint_iff.mpr hDZ₂
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
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let S₀ := (T : Subgroup G) ⊓ normalizer (V₁ : Set G)
  have hSne : S₀ ≠ (T : Subgroup G) := by
    intro he
    have hh : S₀.relIndex (T : Subgroup G) = 2 := s.stabilizer_index
    rw [he,relIndex_self] at hh
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt
    (lt_of_le_of_ne (show S₀ ≤ (T : Subgroup G) from inf_le_left) hSne)
  have hex := s.exchanges t ht (fun hh => htS ⟨ht,hh⟩)
  have hFm : F.map (MulAut.conj t).toMonoidHom = F :=
    mem_normalizer_iff_map_conj_eq.mp (hMcF (hTMc ht))
  have hnon (i : d.Index) : ¬F ≤ centralizer (plane V (c.ambientFactor d i).space : Set G) := by
    have htransfer (A B : Subgroup G)
        (he : A.map (MulAut.conj t).toMonoidHom = B)
        (hh : F ≤ centralizer (A : Set G)) : F ≤ centralizer (B : Set G) := by
      have hm := (map_mono (f := (MulAut.conj t).toMonoidHom) hh).trans
        (map_centralizer_le_centralizer_image (A : Set G) (MulAut.conj t).toMonoidHom)
      simpa only [hFm, ←Subgroup.coe_map,he] using hm
    intro hh
    apply hnFV
    rw [hCV]
    rcases s.covers i with hi | hi
    · rw [hi] at hh
      exact le_inf hh (htransfer V₁ V₂ hex.1 hh)
    · rw [hi] at hh
      exact le_inf (htransfer V₂ V₁ hex.2 hh) hh
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
  intro i
  let Vi := plane V (c.ambientFactor d i).space
  let Zi := thompsonPlane T V (c.ambientFactor d i).space
  let Ai := actionSubgroup ρ (Vi.subgroupOf Mc)
  let Pi := dF.imageSpace Zi
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hViMc : Vi ≤ Mc := (plane_le _).trans hVMc
  have hZiF : Zi ≤ F := (show Zi ≤ E from inf_le_right).trans hEF
  have hidxi : (centralizer (Vi : Set G)).relIndex F ≤ 2 := by
    rcases s.covers i with hi | hi
    · simpa only [Vi,hi] using hidx₁
    · simpa only [Vi,hi] using hidx₂
  obtain ⟨f,hf,hfn⟩ := Set.not_subset.mp (hnon i)
  have hthin : K ⊓ Vi ≤ Zi := fun v hv => hsupport i f hf hfn v hv.2 (hcommD f hf v hv.1)
  have hsmall : Nat.card (K ⊓ Vi : Subgroup G) ≤ 4 :=
    (card_le_of_le hthin).trans_eq (s.thompson_card i)
  have hcount := relIndex_mul_card_of_le (show K ⊓ Vi ≤ Vi from inf_le_right)
  rw [inf_relIndex_right,s.support_card i] at hcount
  have hlower : 4 ≤ K.relIndex Vi := by nlinarith
  have hc : Nat.card Ai = K.relIndex Vi := by
    change Nat.card ((Vi.subgroupOf Mc).map (Representation.BinaryOffender.actionHom ρ)) = _
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective (Representation.BinaryOffender.actionHom ρ).ker
      (Vi.subgroupOf Mc) Mc.subtype_injective
    rw [hkm,map_subgroupOf_eq_of_le hViMc] at he
    exact he.symm
  let : IsElementaryAbelian 2 Vi := IsElementaryAbelian.of_le (plane_le _)
  let : IsElementaryAbelian 2 (Vi.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hViMc
  have he : IsElementaryTwo Ai := by
    refine ⟨?_,IsElementaryAbelian.map (Representation.BinaryOffender.actionHom ρ)⟩
    intro hz
    rw [hz,Subgroup.card_bot] at hc
    omega
  let : IsElementaryAbelian 2 Ai := he.2
  have hrlo : 2 ≤ rank Ai := by
    have hh : 2^2 ≤ 2^rank Ai := by
      have hh' : 4 ≤ Nat.card Ai := hc.symm ▸ hlower
      simpa only [he.card_eq_two_pow_rank, Nat.reducePow] using hh'
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hfix : fixedCodim σ Ai ≤ 1 := by
    have hb := (dF.fixed_quotient_card_le_centralizer_index σ
      (Representation.BinaryOffender.actionHom ρ) Vi).trans hidxi
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (show 2^fixedCodim σ Ai ≤ 2^1 from hb)
  have hPi : Module.finrank (ZMod 2) Pi = 2 := by
    apply dF.imageSpace_finrank_of_index Zi hZiF 2
    have hh := relIndex_mul_card_of_le (show D ⊓ Zi ≤ Zi from inf_le_right)
    rw [inf_relIndex_right,(disjoint_iff.mp (hdis i)),card_bot,s.thompson_card i,mul_one] at hh
    exact hh
  have hcomm : ⁅Vi,F⁆ ≤ Zi := by
    apply commutator_le.mpr
    intro v hv f hf
    have hh := (s.involution_support_displacement_and_fixed
      hM.1.2 h.normalized c d π hp hs hfive f (hFT hf)
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf) (hFN₁ hf) i).2 v hv
    rw [←commutatorElement_inv]
    exact Zi.inv_mem hh
  have hm : subspaceCommutator σ ⊤ Ai ≤ Pi := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨x,hx,rfl⟩,v,_,rfl⟩
    exact dF.displacement_range_le_imageSpace_of_commutator_le Vi Zi hcomm x hx ⟨v,rfl⟩
  have hdim : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ Ai) ≤ 2 :=
    (Submodule.finrank_mono hm).trans_eq hPi
  have hpos := fixedCodim_pos_of_faithful σ (imageRepresentation_injective ρ) he.1
  have hfixeq : fixedCodim σ Ai = 1 := by omega
  have hrhi := DecomposableQuinticControl.rank_le_twice_fixedCodim_of_moved_plane
    σ (imageRepresentation_injective ρ) Ai Ai le_rfl hdim
  rw [hfixeq] at hrhi
  have hreq : rank Ai = 2 := by omega
  have hmin := DecomposableQuinticControl.minimalBestOffender_of_moved_plane_exact_cost
    σ (imageRepresentation_injective ρ) Ai he hdim (Or.inl ⟨hreq,hfixeq⟩)
  have hstrong : IsStrongOffender σ Ai := ⟨he,by rw [hfixeq,hreq]; decide⟩
  have hdimlo := rank_le_fixedCodim_mul_dual σ (imageRepresentation_injective ρ) Ai
  rw [hreq,hfixeq,one_mul,fixedCodim_dual_eq_moved_finrank] at hdimlo
  have hdeq : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ Ai) = Module.finrank (ZMod 2) Pi := by
    rw [hPi]
    omega
  exact ⟨hreq,hfixeq,hmin,hstrong,Submodule.eq_of_le_of_finrank_eq hm hdeq⟩

end CFSG.Quasithin.Chapter15.Section01
