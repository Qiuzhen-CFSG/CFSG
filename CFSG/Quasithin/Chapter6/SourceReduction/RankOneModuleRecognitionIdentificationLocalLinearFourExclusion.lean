module
public import Theory.Representation.SL3FourNaturalContainment
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.GroupTheory.PrimeRankNormalKernel
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalBinaryExclusion
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SeedPlaneMarked
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeActor
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology

/-!
# Excluding SL₃(4) from the original field-plane action

The marked B.5 seed identifies the full component moved space with the
natural SL₃(4) module. Its central extension splits by the established
larger-field SL₃ cohomology theorem.

Restrict the original cubic action to this space. The ambient cubic-rank
bound makes its kernel prime to three; the natural-normalizer theorem
A.3.19 then places the cubic in the actual lifted component. That lift
lies in C_G(U), whereas the original field-plane residual has a two-group
intersection with C_G(U), contradicting the cubic's order.

The Chapter 12 companion retains the original action, quotient coordinates,
and offender, leaving only the A₅ component case. The A₅ exclusion and
subsequent graph argument remain required for LocalAnalysis.
Source: Aschbacher--Smith 6.2.7, printed pp.683--684, using A.3.19, p.54,
and B.4.2, B.5.1, pp.85--86,99--103.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction

private theorem seed_linear_four_natural
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {K A : Subgroup D}
    (hKA : ⁅K,A⁆ = K) (p : Prepared ρ KnownSimple.IsKnownSimple hKA)
    (q : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hKA) (seedComponentImage ρ hKA))
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (hm : moved (seedQuotientAction ρ hKA) (seedComponentImage ρ hKA) = ⊤)
    (eK : K ≃* SL(3,BinaryField.four.Carrier)) :
    ∃ F : BinaryField, F.degree = 2 ∧
      Nonempty (ActionEquiv (seedComponentAction ρ hKA) (linearNatural F 3)) := by
  let e := Preparation.seedComponentEquiv ρ hKA p.component_faithful
  let mark := e.symm.trans eK
  rcases SmallMoved.source_irreducible_or_binary_of_plane (seedQuotientAction ρ hKA)
      (p.minimal.1.isOffender _) (seedOffender_moved_le ρ hKA hd)
      q.sectionData q.clause_one with hi | ⟨d,hd,⟨a⟩⟩
  · obtain ⟨F,⟨a⟩⟩ := SourceCompletion.linearThree_natural_of_irreducible_source
      q.sectionData.action hi.2.2.2 BinaryField.four (by decide) mark
    have hF : F.degree = 2 :=
      (SourceCompletion.linearThree_degree_eq BinaryField.four F
        (mark.symm.trans a.groupEquiv)).symm
    have hz := ThreeCovers.seed_fixed_eq_bot_of_large ρ hKA p q.sectionData hm hi.1
      F (by omega) a
    exact ⟨F,hF,⟨ThreeCovers.transAction (seedComponentActionEquiv ρ hKA p)
      (ThreeCovers.naturalOfWholeSection q.sectionData hm hz a)⟩⟩
  · exact (SourceCompletion.no_linearThree_binary_equiv BinaryField.four hd
      (mark.symm.trans a.groupEquiv)).elim

/-- The SL₃(4) row acts naturally on its original full moved space. -/
theorem linear_four_component_natural
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    {K A : Subgroup D} (hK : IsComponent D K) (hA : IsMinimalBestOffender ρ A)
    (hKA : ⁅K,A⁆ = K) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (eK : K ≃* SL(3,BinaryField.four.Carrier)) :
    ∃ F : BinaryField, F.degree = 2 ∧
      IsLinearNatural ((invariantSubspace ρ K (moved ρ K)
        (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation) F 3 := by
  let N := offenderSubgroup ρ
  obtain ⟨hKN,hAN,hcomm,p,⟨q⟩,hseed,hm⟩ :=
    component_marked_seed_of_minimal_plane ρ hf hcore cover hK hA hKA hd
  have hmove : moved (ρ.comp N.subtype) (K.subgroupOf N) = moved ρ K := by
    change subspaceCommutator (ρ.comp N.subtype) ⊤ (K.subgroupOf N) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKN]
  have hdN : Module.finrank (ZMod 2) (moved (ρ.comp N.subtype) (A.subgroupOf N)) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp N.subtype) ⊤ (A.subgroupOf N)) ≤ 2
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAN]
    exact hd
  obtain ⟨F,hF,⟨a⟩⟩ := seed_linear_four_natural (ρ.comp N.subtype) hcomm p q hdN hm
    ((subgroupOfEquivOfLe hKN).trans eK)
  have he : naturalSeedSpace (ρ.comp N.subtype) (K.subgroupOf N) (A.subgroupOf N) =
      moved ρ K := hseed.trans hmove
  let b : ActionEquiv ((invariantSubspace ρ K (moved ρ K)
      (subspaceCommutator_invariant ρ ⊤ K)).toRepresentation)
      (seedComponentAction (ρ.comp N.subtype) hcomm) :=
    ⟨(subgroupOfEquivOfLe hKN).symm,(LinearEquiv.ofEq _ _ he).symm,
      fun k w => by apply Subtype.ext; rfl⟩
  exact ⟨F,hF,⟨ThreeCovers.transAction b a⟩⟩
private theorem cubic_mem_of_natural_image
    {X : Type*} [Group X] [Finite X]
    (F : BinaryField) (hF : F.degree = 2)
    (K : Subgroup X) [K.Normal]
    (ρ : Representation (ZMod 2) X (Fin 3 → F.Carrier))
    (hr : primeRank 3 X ≤ 2) (hrK : 2 ≤ primeRank 3 K)
    (hk : K ⊓ ρ.ker ≤ pCore 2 X)
    (e : (K.map (actionHom ρ)) ≃* SL(3,F.Carrier))
    (hnat : ∀ (j : K.map (actionHom ρ)) (v : Fin 3 → F.Carrier),
      imageRepresentation ρ j v = (e j).val.mulVec v)
    (x : X) (hx : x ^ 3 = 1) : x ∈ K := by
  let f := actionHom ρ
  let J := K.map f
  let : J.Normal := (inferInstance : K.Normal).map f ρ.asGroupHom.rangeRestrict_surjective
  let a : ActionEquiv ((imageRepresentation ρ).comp J.subtype) (linearNatural F 3) :=
    ⟨e,LinearEquiv.refl _ _,hnat⟩
  have hi := CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv a
    (CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.linearNatural_irreducible F (by decide))
  let := irreducible_of_subgroup_restriction (imageRepresentation ρ) J hi
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff f
    ρ.asGroupHom.rangeRestrict_surjective (imageRepresentation ρ)).mpr inferInstance
  have hcore : pCore 2 X ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hcop := coprime_three_card_of_normal_disjoint_mod_core K ρ.ker hcore hk hrK hr
  have hfker : f.ker = ρ.ker := by
    ext g
    change f g = 1 ↔ ρ g = 1
    constructor
    · intro he
      exact congrArg (imageRepresentation ρ) he
    · intro he
      apply imageRepresentation_injective
      exact he
  have hrim : primeRank 3 (actionImage ρ) ≤ 2 :=
    (primeRank_le_of_surjective_of_coprime 3 f ρ.asGroupHom.rangeRestrict_surjective
      (hfker.symm ▸ hcop)).trans hr
  have hres := SL3FourNaturalContainment.pResidual_le_of_natural
    (F.card_eq.trans (by rw [hF]; decide)) J e (imageRepresentation ρ)
    (imageRepresentation_injective ρ) hnat hrim
  have hxres : f x ∈ pResidual 2 (actionImage ρ) :=
    mem_pResidual_of_orderOf_coprime (by
      have ho : orderOf (f x) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hx,map_one])
      exact (by decide : Nat.Coprime 2 3).of_dvd_right ho)
  obtain ⟨k,hkK,hkx⟩ := hres hxres
  let q := QuotientGroup.mk' K
  have hc : x * k⁻¹ ∈ ρ.ker := by
    rw [←hfker]
    change f (x * k⁻¹) = 1
    rw [map_mul,map_inv,hkx,mul_inv_cancel]
  have hqx : q x ∈ ρ.ker.map q := by
    refine ⟨x*k⁻¹,hc,?_⟩
    rw [map_mul,map_inv,show q k = 1 from (QuotientGroup.eq_one_iff k).mpr hkK,inv_one,mul_one]
  let z : ρ.ker.map q := ⟨q x,hqx⟩
  have hz3 : z^3=1 := Subtype.ext (show (q x)^3=1 from by rw [←map_pow,hx,map_one])
  have hc' : Nat.Coprime 3 (Nat.card (ρ.ker.map q)) :=
    hcop.coprime_dvd_right (card_dvd_of_surjective (q.subgroupMap ρ.ker)
      (q.subgroupMap_surjective ρ.ker))
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc'
    (orderOf_dvd_of_pow_eq_one hz3) (orderOf_dvd_natCard z))
  exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hz1)

private theorem cubic_mem_of_natural_quotient
    {X : Type*} [Group X] [Finite X]
    (F : BinaryField) (hF : F.degree = 2)
    (K : Subgroup X) [K.Normal]
    (ρ : Representation (ZMod 2) X (Fin 3 → F.Carrier))
    (κ : K →* SL(3,F.Carrier)) (hκ : Function.Surjective κ)
    (hκtwo : IsPGroup 2 κ.ker)
    (hnat : ∀ (k : K) (v : Fin 3 → F.Carrier), ρ k v = (κ k).val.mulVec v)
    (hr : primeRank 3 X ≤ 2) (x : X) (hx : x ^ 3 = 1) : x ∈ K := by
  let f := actionHom ρ
  let J := K.map f
  let j := f.subgroupMap K
  have hj : Function.Surjective j := f.subgroupMap_surjective K
  have hk : j.ker = κ.ker := by
    ext k
    change j k = 1 ↔ κ k = 1
    constructor
    · intro hk
      apply SmallMoved.linearNatural_faithful F 3
      apply LinearMap.ext
      intro v
      have hh := congrArg (fun a : J => imageRepresentation ρ a v) hk
      change ρ k v = v at hh
      rw [map_one]
      change (κ k).val.mulVec v = v
      exact (hnat k v).symm.trans hh
    · intro hk
      apply Subtype.ext
      apply imageRepresentation_injective ρ
      apply LinearMap.ext
      intro v
      change ρ k v = v
      rw [hnat,hk]
      simp
  let e : J ≃* SL(3,F.Carrier) :=
    (QuotientGroup.quotientKerEquivOfSurjective j hj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective κ hκ))
  have he (k : K) : e (j k) = κ k := by
    change e ((QuotientGroup.quotientKerEquivOfSurjective j hj)
      (QuotientGroup.mk' j.ker k)) = κ k
    simp only [e,MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    rfl
  have hmark (a : J) (v : Fin 3 → F.Carrier) :
      imageRepresentation ρ a v = (e a).val.mulVec v := by
    obtain ⟨k,rfl⟩ := hj a
    rw [he]
    exact hnat k v
  have hker : IsPGroup 2 (K ⊓ ρ.ker : Subgroup X) := by
    let i : (K ⊓ ρ.ker : Subgroup X) →* j.ker := {
      toFun a := ⟨⟨a,a.property.1⟩,by
        apply Subtype.ext
        apply imageRepresentation_injective ρ
        exact a.property.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hi : Function.Injective i := by
      intro a b hab
      exact Subtype.ext (congrArg (fun t : j.ker => (t.val : X)) hab)
    exact (hk.symm ▸ hκtwo).of_injective i hi
  have hkle : K ⊓ ρ.ker ≤ pCore 2 X := le_sSup ⟨inferInstance,hker⟩
  have hrK : 2 ≤ primeRank 3 K := by
    have hc : Nat.Coprime 3 (Nat.card κ.ker) := by
      obtain ⟨n,hn⟩ := hκtwo.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    have hm := Matrix.PSL3.SplitPrimeRank.special_rank F.Carrier
      (p := 3) (by rw [F.card_eq,hF]; decide)
    exact hm.trans (primeRank_le_of_surjective_of_coprime 3 κ hκ hc)
  exact cubic_mem_of_natural_image F hF K ρ hr hrK hkle e hmark x hx

private theorem cubic_mem_of_moved_natural
    {P D W : Type*} [Group P] [Finite P] [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (η : Representation (ZMod 2) P W) (ρ : Representation (ZMod 2) D W)
    (K : Subgroup P) (J : Subgroup D) (κ : K →* J) (hκ : Function.Surjective κ)
    (hκtwo : IsPGroup 2 κ.ker)
    (hres : ∀ k : K, η k = ρ (κ k))
    (F : BinaryField) (hF : F.degree = 2)
    (a : ActionEquiv ((invariantSubspace ρ J (moved ρ J)
      (subspaceCommutator_invariant ρ ⊤ J)).toRepresentation) (linearNatural F 3))
    (hr : primeRank 3 P ≤ 2)
    (d : P) (hd : d ∈ normalizer (K : Set P)) (hd3 : d ^ 3 = 1) : d ∈ K := by
  let X := K ⊔ zpowers d
  have hXK : X ≤ normalizer (K : Set P) := sup_le K.le_normalizer (zpowers_le.mpr hd)
  let K0 := K.subgroupOf X
  let : K0.Normal := normal_subgroupOf_of_le_normalizer hXK
  let eK : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let U := moved ρ J
  have hmove : moved η K = U := by
    have he : η.comp K.subtype = ρ.comp (J.subtype.comp κ) := by
      ext k w
      exact LinearMap.congr_fun (hres k) w
    calc
      moved η K = moved (η.comp K.subtype) ⊤ := by
        simp only [moved,subspaceCommutator_comp_map,← MonoidHom.range_eq_map,range_subtype]
      _ = moved (ρ.comp (J.subtype.comp κ)) ⊤ := congrArg (fun t => moved t ⊤) he
      _ = U := by
        rw [moved,subspaceCommutator_comp_map,← MonoidHom.range_eq_map]
        have hh : (J.subtype.comp κ).range = J := by
          rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hκ,← MonoidHom.range_eq_map,range_subtype]
        rw [hh]
  have hU : X ≤ subspaceStabilizer η U := hmove ▸
    subspaceCommutator_invariant_normalizer η (le_subspaceStabilizer η ⊤ (by simp)) hXK
  let τ := (invariantSubspace η X U hU).toRepresentation
  let σ : Representation (ZMod 2) X (Fin 3 → F.Carrier) :=
    a.linearEquiv.conjRingEquiv.toMonoidHom.comp τ
  let μ : K0 →* SL(3,F.Carrier) := a.groupEquiv.toMonoidHom.comp (κ.comp eK.toMonoidHom)
  have hμ : Function.Surjective μ := a.groupEquiv.surjective.comp (hκ.comp eK.surjective)
  have hμtwo : IsPGroup 2 μ.ker := by
    let i : μ.ker →* κ.ker := {
      toFun k := ⟨eK k.val,by
        apply a.groupEquiv.injective
        have hh : a.groupEquiv (κ (eK k.val)) = 1 := k.property
        simpa only [map_one] using hh⟩
      map_one' := by apply Subtype.ext; exact eK.map_one
      map_mul' _ _ := by apply Subtype.ext; exact eK.map_mul _ _ }
    apply hκtwo.of_injective i
    intro k l hkl
    apply Subtype.ext
    apply eK.injective
    exact congrArg Subtype.val hkl
  have hnat (k : K0) (v : Fin 3 → F.Carrier) : σ k v = (μ k).val.mulVec v := by
    change a.linearEquiv (τ k (a.linearEquiv.symm v)) = (μ k).val.mulVec v
    have ht : τ k (a.linearEquiv.symm v) =
        (invariantSubspace ρ J U (subspaceCommutator_invariant ρ ⊤ J)).toRepresentation
          (κ (eK k)) (a.linearEquiv.symm v) := by
      apply Subtype.ext
      exact LinearMap.congr_fun (hres (eK k)) _
    rw [ht,a.intertwines,a.linearEquiv.apply_symm_apply]
    rfl
  have hmem := cubic_mem_of_natural_quotient F hF K0 σ μ hμ hμtwo hnat
    ((primeRank_subgroup_le 3 X).trans hr) (⟨d,mem_sup_right (mem_zpowers d)⟩ : X)
    (Subtype.ext hd3)
  exact hmem

private theorem field_linear_four_natural_excluded
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n) (hUc : Nat.card U = 4)
    (hout : ¬ Centralizer U ≤ normalizer (layer L R : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (action (layer L R) U).range W)
    (c : BinaryConjugationSection (Centralizer U)
      (conjugateSpanBy (layer L R) (Centralizer U)) U
      (ρ.comp (action (layer L R) U).rangeRestrict))
    (J : Subgroup (action (layer L R) U).range) (hJ : IsComponent _ J)
    (F : BinaryField) (hF : F.degree = 2)
    (aF : ActionEquiv ((invariantSubspace ρ J (moved ρ J)
      (subspaceCommutator_invariant ρ ⊤ J)).toRepresentation) (linearNatural F 3)) : False := by
  let B := layer L R
  let H := Centralizer U
  let P := H ⊔ fieldLocalResidual L U
  let π := (action B U).rangeRestrict
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hUB : U ≤ B := hfield.choose_spec.2.2.1.le.trans inf_le_left
  let : IsElementaryAbelian 2 (conjugateSpanBy B H) :=
    local_plane_closure_elementary h hnatural hE hfactor hUB hUc.ge
  obtain ⟨d,hd,ho,_,η,_,_,hrestrict,_⟩ := field_plane_cubic_section_action hnat hfield hUc c
  let dP : P := ⟨d,mem_sup_right hd⟩
  have hd3 : d^3=1 := ho ▸ pow_orderOf_eq_one d
  obtain ⟨K,hK,_,eQ,heQ⟩ := action_component_lift h hnatural hE hfactor hu hfield hUc hout J hJ
  let : IsQuasisimple J := hJ.2
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eQ.symm
  obtain ⟨α,_,hα⟩ := local_field_cubic_component_action h hfield hUc K hK d hd hd3
  let i : H →* P := inclusion le_sup_left
  let K0 := K.map i
  let e : K ≃* K0 := K.equivMapOfInjective i (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 K)
  let κ : K0 →* J := eQ.toMonoidHom.comp (q.comp e.symm.toMonoidHom)
  have hκ : Function.Surjective κ := eQ.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)
  have hκtwo : IsPGroup 2 κ.ker := by
    let j : κ.ker →* pCore 2 K := {
      toFun k := ⟨e.symm k.val,by
        have hh : eQ (q (e.symm k.val)) = 1 := k.property
        exact (QuotientGroup.eq_one_iff _).mp (eQ.map_eq_one_iff.mp hh)⟩
      map_one' := by apply Subtype.ext; exact e.symm.map_one
      map_mul' _ _ := by apply Subtype.ext; exact e.symm.map_mul _ _ }
    apply pCore_isPGroup.of_injective j
    intro k l he
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val he
  have hres (k : K0) : η k = ρ (κ k) := by
    have he : i (e.symm k : H) = (k : P) :=
      congrArg Subtype.val (e.apply_symm_apply k)
    rw [←he,hrestrict]
    change ρ (π (e.symm k)) = ρ (κ k)
    exact congrArg ρ (heQ (e.symm k)).symm
  have hnorm : dP ∈ normalizer (K0 : Set P) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨k,hk,rfl⟩
      obtain ⟨b,hb,rfl⟩ := hk
      exact ⟨(α ⟨b,hb⟩ : H),(α ⟨b,hb⟩).property,Subtype.ext (hα ⟨b,hb⟩)⟩
    · exact (card_map_of_injective (K := K0) (MulAut.conj dP).injective).ge
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hPN : P ≤ normalizer (U : Set G) := sup_le (Subgroup.centralizer_le_normalizer _)
    ((map_subtype_le _).trans inf_le_right)
  have hr : primeRank 3 P ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hPN)
      (inclusion_injective _)).trans
      ((local_field_normalizer_sqtk h hfield hUne).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hdK := cubic_mem_of_moved_natural η ρ K0 J κ hκ hκtwo hres F hF aF hr dP hnorm
    (Subtype.ext hd3)
  have hdH : d ∈ H := by
    obtain ⟨k,_,he⟩ := hdK
    have hv : (k : G) = d := congrArg Subtype.val he
    exact hv ▸ k.property
  have hdcore : d ∈ (fieldLocalResidual L U).pCoreIn 2 := by
    rw [(field_plane_residual_structure hnat hfield hUc).1]
    exact ⟨hd,hdH⟩
  obtain ⟨b,hb,hbd⟩ := hdcore
  have hcop := (pCore_isPGroup (p := 2) (G := fieldLocalResidual L U)).orderOf_coprime
    (show Nat.Coprime 2 3 by decide) ⟨b,hb⟩
  have hbo : orderOf (⟨b,hb⟩ : pCore 2 (fieldLocalResidual L U)) = 3 := by
    let f := (fieldLocalResidual L U).subtype.comp
      (pCore 2 (fieldLocalResidual L U)).subtype
    have hf := (fieldLocalResidual L U).subtype_injective.comp
      (pCore 2 (fieldLocalResidual L U)).subtype_injective
    calc
      _ = orderOf (b : G) := (orderOf_injective f hf ⟨b,hb⟩).symm
      _ = 3 := by rw [show (b : G) = d from hbd,ho]
  rw [hbo] at hcop
  norm_num at hcop


/-- The actual cubic and its component lift exclude SL₃(4) in the
original one-sided plane-offender configuration. -/
theorem one_sided_linear_four_component_excluded
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (action (layer L R)
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).range W)
    (c : BinaryConjugationSection
      (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)))
      (conjugateSpanBy (layer L R)
        (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))))
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
      (ρ.comp (action (layer L R)
        (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).rangeRestrict))
    (hf : Function.Injective ρ) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (Centralizer U)).map (action B U).rangeRestrict
    IsMinimalBestOffender ρ I →
    ∀ K, IsComponent (action B U).range K → ⁅K,I⁆ = K →
      ¬ Nonempty (K ≃* SL(3,BinaryField.four.Carrier)) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let f := action B U
  dsimp only
  intro hI K hK hKI ⟨eK⟩
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h hnatural hE hfactor g hBA hnon
  have hdim := (section_plane_geometry h hnatural hE hfactor g hBA hnon ρ c).2.2.1
  have hUc' : Nat.card U = 4 := hUc
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc'; contradiction
  let cover : SQTKQuotient KnownSimple.IsKnownSimple f.range := {
    Cover := H
    kernel := f.ker
    sqtk := by
      let j : H →* normalizer (U : Set G) := inclusion (Subgroup.centralizer_le_normalizer _)
      have hs := local_field_normalizer_sqtk h hfield hUne
      exact ⟨hs.stronglyQuasithin.of_injective j (inclusion_injective _),
        hs.isKGroup.of_injective j (inclusion_injective _)⟩
    equiv := QuotientGroup.quotientKerEquivRange f }
  obtain ⟨F,hF,⟨aF⟩⟩ := linear_four_component_natural ρ hf
    (action_range_core h hnatural hE hfactor hfield hUc.ge) cover hK hI hKI hdim eK
  exact field_linear_four_natural_excluded h hnatural hE hfactor hu hfield hUc hout
    ρ c K hK F hF aF

/-- The original marked plane section after excluding both linear-three components. -/
@[expose] def PlaneAlternatingSection {G : Type*} [Group G] [Finite G]
    (B A U : Subgroup G) [IsElementaryAbelian 2 (LocalFieldQuotientAction.space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range
        (Additive (LocalFieldQuotientAction.space B U)))
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ IsQuadratic ρ I ∧ Nat.card I = 4 ∧
      moved ρ I = c.imageSpace ⁅A,B⁆ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2 ∧
      fixedCodim ρ I = 2 ∧ I ∈ ChapterE.fixedSpaceFamily ρ 2 ∧
      IsMinimalBestOffender ρ I ∧
      (∀ K, IsComponent (LocalFieldQuotientAction.action B U).range K → ⁅K,I⁆ = K →
        IsIrrPlus ρ K (moved ρ K) ∧
          Nonempty (K ≃* alternatingGroup (Fin 5))) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
