module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoDisjointStrong
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionBestGeometry
public import Theory.Representation.CyclicFixedRank
public import Theory.Representation.BinaryOffender.CommutatorRank
-- Same source proof split: the support index lemma remains in its frozen owner.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# Original support actors on the two-line canonical section

The images of the two marked planes are literal lines in F/D. Each
original support actor moves within its line and has fixed codimension
at most one. Faithful displacement counting therefore bounds each
support actor image by two, and their original join by four.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v

private theorem card_le_pow_fixedCodim_of_moved_line
    {J W : Type*} [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (hf : Function.Injective σ) (B : Subgroup J) (P : Submodule (ZMod 2) W)
    (hm : subspaceCommutator σ ⊤ B ≤ P) (hd : Module.finrank (ZMod 2) P ≤ 1) :
    Nat.card B ≤ 2 ^ fixedCodim σ B := by
  let C := fixedSpace σ B
  let δ (b : B) : (W ⧸ C) →ₗ[ZMod 2] P :=
    C.liftQ ((σ b - LinearMap.id).codRestrict P
      (fun w => hm (Submodule.subset_span ⟨b,b.property,w,Submodule.mem_top,rfl⟩)))
      (by intro w hw; exact Subtype.ext (sub_eq_zero.mpr (hw b)))
  have hδ : Function.Injective δ := by
    intro a b he
    apply Subtype.ext
    apply hf
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun z : (W ⧸ C) →ₗ[ZMod 2] P => (z (C.mkQ w) : W)) he
    exact sub_left_injective hh
  let : Finite ((W ⧸ C) →ₗ[ZMod 2] P) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective δ hδ
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ((W ⧸ C) →ₗ[ZMod 2] P)),Nat.card_zmod,Module.finrank_linearMap] at hc
  change Nat.card B ≤ 2 ^ (fixedCodim σ B * Module.finrank (ZMod 2) P) at hc
  exact hc.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

private theorem moved_dimension_eq_cost_of_card_two
    {J W : Type*} [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (A : Subgroup J) (hc : Nat.card A = 2) :
    Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = fixedCodim σ A := by
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨a,ha⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  rw [←ha,Representation.CyclicFixedRank.commutator_eq_range,
    fixedCodim_zpowers_eq_displacement_rank]

private theorem minimal_best_of_card_two
    {J W : Type*} [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (A : Subgroup J) (hA : IsOffender σ A) (hc : Nat.card A = 2) :
    IsMinimalBestOffender σ A := by
  have hsub (B : Subgroup J) (hBA : B ≤ A) : B = ⊥ ∨ B = A := by
    have hd : Nat.card B ∣ 2 := hc ▸ card_dvd_of_le hBA
    have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    rw [show Nat.divisors 2 = {1,2} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hb | hb
    · exact Or.inl (Subgroup.card_eq_one.mp hb)
    · exact Or.inr (eq_of_le_of_card_ge hBA (by omega))
  refine ⟨⟨hA.1,?_⟩,?_⟩
  · intro B hBA
    rcases hsub B hBA with hb | hb
    · rw [hb,weight_bot]
      exact (fixedCodim_le_rank_iff σ A).mp hA.2
    · rw [hb]
  · intro B hB hBA
    exact (hsub B hBA.1).resolve_left hB.1.1

variable {G : Type u} [Group G] [Finite G]

/-- Each actual support image has order at most two in the remaining
canonical two-line branch. The original actor, kernel and moved space stay fixed. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_actor_bounds
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
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      let V₁ := plane V (c.ambientFactor d s.first).space
      let V₂ := plane V (c.ambientFactor d s.second).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let A₁ := actionSubgroup ρ (V₁.subgroupOf Mc)
          let A₂ := actionSubgroup ρ (V₂.subgroupOf Mc)
          IsOffender σ A ∧ IsQuadratic σ A ∧
            dF.imageSpace E = subspaceCommutator σ ⊤ A ∧
            Module.finrank (ZMod 2) (dF.imageSpace Z₁) = 1 ∧
            Module.finrank (ZMod 2) (dF.imageSpace Z₂) = 1 ∧
            (Module.finrank (ZMod 2) (dF.imageSpace E) = 1 ∨
              Module.finrank (ZMod 2) (dF.imageSpace E) = 2) ∧
            A₁ ⊔ A₂ = A ∧ Nat.card A₁ ≤ 2 ∧ Nat.card A₂ ≤ 2 ∧
            Nat.card A ≤ 4 ∧
            Nat.card A = (commutatorPreimage Mc F D).relIndex V := by
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
  intro W _ _ ρ dF hline
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let A₁ := actionSubgroup ρ (V₁.subgroupOf Mc)
  let A₂ := actionSubgroup ρ (V₂.subgroupOf Mc)
  have hfaith : Function.Injective σ := imageRepresentation_injective ρ
  obtain ⟨hDF,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
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
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
  have hnFV : ¬F ≤ centralizer (V : Set G) := by
    intro hc
    apply hDF.not_ge
    intro f hf
    refine ⟨⟨f,dF.section_le hf⟩,?_,rfl⟩
    intro n
    have hf' := le_normalizer_iff.mp dF.normalized n n.property f hf
    exact ⟨hf',hc hf'⟩
  obtain ⟨_,hne,hindex⟩ := h.decomposable_five_normal_section_indices
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
    F D hDF.le le_rfl hDF hnD hnFV
  change 1 < K.relIndex V at hne
  have hk : (Representation.BinaryOffender.actionHom ρ).ker = ρ.ker := by
    ext a
    change Representation.BinaryOffender.actionHom ρ a = 1 ↔ ρ a = 1
    rw [actionHom_eq_one_iff]
    exact ⟨fun he => LinearMap.ext he,fun he v => LinearMap.congr_fun he v⟩
  have hkm : (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype = K := by
    rw [hk]
    exact dF.action_kernel_map hnD
  have hcardA : Nat.card A = K.relIndex V := by
    change Nat.card ((V.subgroupOf Mc).map (Representation.BinaryOffender.actionHom ρ)) = _
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective (Representation.BinaryOffender.actionHom ρ).ker
      (V.subgroupOf Mc) Mc.subtype_injective
    rw [hkm,map_subgroupOf_eq_of_le hVMc] at he
    exact he.symm
  let : IsElementaryAbelian 2 (V.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hVMc
  have heA : IsElementaryTwo A := by
    refine ⟨?_,IsElementaryAbelian.map (Representation.BinaryOffender.actionHom ρ)⟩
    intro he
    rw [he,Subgroup.card_bot] at hcardA
    omega
  let : IsElementaryAbelian 2 A := heA.2
  have hoff : IsOffender σ A := by
    apply BinaryConjugationSection.offender_of_section_index σ
      (Representation.BinaryOffender.actionHom ρ) dF V (centralizer (V : Set G))
    · rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr le_rfl]
      exact bot_le
    · exact heA
    · change (centralizer (V : Set G)).relIndex F ≤ Nat.card A
      rwa [hcardA]
  have hVF : ⁅V,F⁆ = E := (h.decomposable_five_moving_normal_span
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
    F le_rfl dF.normalized hnFV).1
  have hquad : IsQuadratic σ A := by
    apply dF.quadratic_of_commutator_bounds σ
      (Representation.BinaryOffender.actionHom ρ) V E hVF.le
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (V.le_centralizer.trans (centralizer_le inf_le_left))).le.trans bot_le
  have hself : dF.imageSpace F = ⊤ := dF.imageSpace_self
  have himage (B : Subgroup G) (hB : B ≤ Mc) :
      dF.imageSpace ⁅B,F⁆ = subspaceCommutator σ ⊤ (actionSubgroup ρ (B.subgroupOf Mc)) := by
    change _ = subspaceCommutator σ ⊤ ((B.subgroupOf Mc).map
      (Representation.BinaryOffender.actionHom ρ))
    rw [←subspaceCommutator_comp_map]
    change dF.imageSpace ⁅B,F⁆ = subspaceCommutator ρ ⊤ (B.subgroupOf Mc)
    simpa only [hself] using dF.imageSpace_commutator B F hB le_rfl
  have himageE : dF.imageSpace E = subspaceCommutator σ ⊤ A := by
    simpa only [hVF] using himage V hVMc
  obtain ⟨hcards,_,_,himages⟩ := (h.decomposable_five_partner_two_seed_intersections
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hline₂ : Nat.card (D ⊓ Z₂ : Subgroup G) = 2 := hcards.symm.trans hline
  have hdimZi (i : d.Index) :
      Module.finrank (ZMod 2) (dF.imageSpace (thompsonPlane T V (c.ambientFactor d i).space)) = 1 := by
    let Zi := thompsonPlane T V (c.ambientFactor d i).space
    have hc : Nat.card (D ⊓ Zi : Subgroup G) = 2 := by
      rcases s.covers i with he | he
      · simpa only [Zi,he] using hline
      · simpa only [Zi,he] using hline₂
    have hm := relIndex_mul_card_of_le (show D ⊓ Zi ≤ Zi from inf_le_right)
    rw [inf_relIndex_right,hc,s.thompson_card i] at hm
    exact dF.imageSpace_finrank_of_index Zi ((show Zi ≤ E from inf_le_right).trans hEF) 1 (by change D.relIndex Zi = 2^1; norm_num; omega)
  obtain ⟨_,_,_,hrows⟩ := himages ρ dF
  have hdimE : Module.finrank (ZMod 2) (dF.imageSpace E) = 1 ∨
      Module.finrank (ZMod 2) (dF.imageSpace E) = 2 := by
    rcases hrows with hthree | htwo | hone
    · have hh := hdimZi s.first
      have hh' := hthree.2.2.1
      omega
    · exact Or.inr htwo.2
    · exact Or.inl hone.2.1
  have hsupport (i : d.Index) :
      Nat.card (actionSubgroup ρ ((plane V (c.ambientFactor d i).space).subgroupOf Mc)) ≤ 2 := by
    let Vi := plane V (c.ambientFactor d i).space
    let Zi := thompsonPlane T V (c.ambientFactor d i).space
    let Ai := actionSubgroup ρ (Vi.subgroupOf Mc)
    have hViV : Vi ≤ V := plane_le _
    have hViMc := hViV.trans hVMc
    have hdisp : ⁅Vi,F⁆ ≤ Zi := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro f hf v hv
      exact (s.involution_support_displacement_and_fixed
        hM.1.2 h.normalized c d π hp hs hfive f (hFT hf)
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf) (hFN₁ hf) i).2 v hv
    have hmove : subspaceCommutator σ ⊤ Ai ≤ dF.imageSpace Zi := by
      rw [←himage Vi hViMc]
      exact dF.imageSpace_mono hdisp
    have hidxi : (centralizer (Vi : Set G)).relIndex F ≤ 2 := by
      rcases s.covers i with he | he
      · simpa only [Vi,he] using hidx₁
      · simpa only [Vi,he] using hidx₂
    have hcost : fixedCodim σ Ai ≤ 1 := by
      have hb := (dF.fixed_quotient_card_le_centralizer_index σ
        (Representation.BinaryOffender.actionHom ρ) Vi).trans hidxi
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hb
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
    exact (card_le_pow_fixedCodim_of_moved_line σ hfaith Ai (dF.imageSpace Zi)
      hmove (hdimZi i).le).trans (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hcost)
  have hAjoin : A₁ ⊔ A₂ = A := by
    change (V₁.subgroupOf Mc).map (Representation.BinaryOffender.actionHom ρ) ⊔
      (V₂.subgroupOf Mc).map (Representation.BinaryOffender.actionHom ρ) =
        (V.subgroupOf Mc).map (Representation.BinaryOffender.actionHom ρ)
    rw [←Subgroup.map_sup,←subgroupOf_sup ((plane_le _).trans hVMc) ((plane_le _).trans hVMc),s.complement]
  have hcA₁ : Nat.card A₁ ≤ 2 := hsupport s.first
  have hcA₂ : Nat.card A₂ ≤ 2 := hsupport s.second
  have hA₁ : A₁ ≤ A := hAjoin ▸ le_sup_left
  have hA₂ : A₂ ≤ A := hAjoin ▸ le_sup_right
  have hcomm : A₂ ≤ centralizer (A₁ : Set (Representation.BinaryOffender.actionImage ρ)) :=
    hA₂.trans (A.le_centralizer.trans (centralizer_le hA₁))
  have hcA : Nat.card A ≤ 4 := by
    have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes A₁ A₂
      (hcomm.trans (Subgroup.centralizer_le_normalizer _))
    rw [hAjoin] at hm
    have hp : 0 < Nat.card (A₁ ⊓ A₂ : Subgroup (Representation.BinaryOffender.actionImage ρ)) := Nat.card_pos
    nlinarith
  exact ⟨hoff,hquad,himageE,hdimZi s.first,hdimZi s.second,hdimE,
    hAjoin,hcA₁,hcA₂,hcA,hcardA⟩

/-- Exact original rank, fixed codimension and section-kernel orders in
the two-line branch. The strong cost is a genuine minimal best offender;
the two equal-cost alternatives are ordinary offenders. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_costs
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
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      let K := commutatorPreimage Mc F D
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let P := dF.imageSpace E
          IsOffender σ A ∧ IsQuadratic σ A ∧ P = subspaceCommutator σ ⊤ A ∧
            Module.finrank (ZMod 2) (dF.imageSpace Z₁) = 1 ∧
            Module.finrank (ZMod 2) (dF.imageSpace Z₂) = 1 ∧
            (Module.finrank (ZMod 2) P = 1 ∨ Module.finrank (ZMod 2) P = 2) ∧
            Nat.card A = K.relIndex V ∧
            ((rank A = 1 ∧ fixedCodim σ A = 1 ∧ Module.finrank (ZMod 2) P = 1 ∧
                K.relIndex V = 2 ∧ Nat.card (K ⊓ V : Subgroup G) = 128 ∧
                IsMinimalBestOffender σ A) ∨
              (rank A = 2 ∧ fixedCodim σ A = 1 ∧ Module.finrank (ZMod 2) P = 2 ∧
                K.relIndex V = 4 ∧ Nat.card (K ⊓ V : Subgroup G) = 64 ∧
                IsStrongOffender σ A ∧ IsMinimalBestOffender σ A) ∨
              (rank A = 2 ∧ fixedCodim σ A = 2 ∧ K.relIndex V = 4 ∧
                Nat.card (K ⊓ V : Subgroup G) = 64 ∧ ¬IsStrongOffender σ A)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let K := commutatorPreimage Mc F D
  rcases h.decomposable_five_partner_two_line_actor_bounds
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | hbound
  · exact Or.inl hcore
  right
  intro W _ _ ρ dF hline
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let P := dF.imageSpace E
  obtain ⟨hoff,hquad,himage,hd₁,hd₂,hdP,_,_,_,hcA,hcard⟩ := hbound ρ dF hline
  change IsOffender σ A at hoff
  change Nat.card A ≤ 4 at hcA
  change Nat.card A = K.relIndex V at hcard
  change P = subspaceCommutator σ ⊤ A at himage
  change Module.finrank (ZMod 2) P = 1 ∨ Module.finrank (ZMod 2) P = 2 at hdP
  have hfaith : Function.Injective σ := imageRepresentation_injective ρ
  have hrpos := hoff.1.rank_pos
  have hcostpos := fixedCodim_pos_of_faithful σ hfaith hoff.1.1
  have hr : rank A ≤ 2 := by
    have hh : 2 ^ rank A ≤ 2^2 := by rw [←hoff.1.card_eq_two_pow_rank]; exact hcA
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  have hmoved : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 2 := by
    rw [←himage]
    omega
  have hcV : Nat.card V = 256 := by
    rw [←s.complement,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _)))).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr s.disjoint),
      s.support_card,s.support_card]
  have hcount := relIndex_mul_card_of_le (show K ⊓ V ≤ V from inf_le_right)
  rw [inf_relIndex_right,hcV] at hcount
  refine ⟨hoff,hquad,himage,hd₁,hd₂,hdP,hcard,?_⟩
  by_cases hr₁ : rank A = 1
  · have hc₁ : fixedCodim σ A = 1 := by have hh := hoff.2; omega
    have hcard₂ : Nat.card A = 2 := by rw [hoff.1.card_eq_two_pow_rank,hr₁]; rfl
    have hi : K.relIndex V = 2 := hcard.symm.trans hcard₂
    have hker : Nat.card (K ⊓ V : Subgroup G) = 128 := by rw [hi] at hcount; omega
    have hdim : Module.finrank (ZMod 2) P = 1 := by
      have hh := moved_dimension_eq_cost_of_card_two σ A hcard₂
      rw [←himage,hc₁] at hh
      exact hh
    exact Or.inl ⟨hr₁,hc₁,hdim,hi,hker,minimal_best_of_card_two σ A hoff hcard₂⟩
  have hr₂ : rank A = 2 := by omega
  have hcard₄ : Nat.card A = 4 := by rw [hoff.1.card_eq_two_pow_rank,hr₂]; rfl
  have hi : K.relIndex V = 4 := hcard.symm.trans hcard₄
  have hker : Nat.card (K ⊓ V : Subgroup G) = 64 := by rw [hi] at hcount; omega
  by_cases hc₁ : fixedCodim σ A = 1
  · have hdim : Module.finrank (ZMod 2) P = 2 := by
      rcases hdP with hdP | hdP
      · have hb := card_le_pow_fixedCodim_of_moved_line σ hfaith A P himage.ge hdP.le
        rw [hcard₄,hc₁] at hb
        norm_num at hb
      · exact hdP
    have hsA : IsStrongOffender σ A := ⟨hoff.1,by omega⟩
    have hmA := DecomposableQuinticControl.minimalBestOffender_of_moved_plane_exact_cost
      σ hfaith A hoff.1 hmoved (Or.inl ⟨hr₂,hc₁⟩)
    exact Or.inr (Or.inl ⟨hr₂,hc₁,hdim,hi,hker,hsA,hmA⟩)
  · have hc₂ : fixedCodim σ A = 2 := by have hh := hoff.2; omega
    have hn : ¬IsStrongOffender σ A := by intro hh; have hh' := hh.2; omega
    exact Or.inr (Or.inr ⟨hr₂,hc₂,hi,hker,hn⟩)

end CFSG.Quasithin.Chapter15.Section01
