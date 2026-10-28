module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefDisplacement
public import Theory.GroupTheory.NoncentralChiefRefinement.MovedChief
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator

/-!
# Constructing the actual partner chief action

In the noncore branch, the characteristic-two centralizer bound on Mc/Z
forces Kc to move Qc/Z. The identity Kc = [Kc,V] and two-perfectness then
give an actual L-chief interval between Z and Qc, where L = Kc T, moved by V.
Its literal quotient carries an irreducible binary action. The two-core of L
acts trivially, so this same action descends to L/O₂(L), retaining a nontrivial
involution of displacement rank one or two.

Passing instead to the faithful action image preserves that involution and
the displacement bound. The image of V is nontrivial, elementary abelian,
quadratic, and normal in the image of the original Sylow subgroup. This does
not yet identify the faithful image with L/O₂(L), exclude rank one, or prove
the model recognition needed by source_chosen_false_of_partner_model_displacement.
Those are the remaining local steps of the critical-pair assembly owner.

The explicit inputs are the preceding source wreath quotients, residual and
structural alternatives, and centralizer/plane marking from 15.2.8--14.
No weak-closure or 15.2.26 conclusion is used.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136), before the B.4.2/B.4.5 recognition step.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Kc acts nontrivially on the literal central quotient Qc/Z. -/
theorem source_chosen_partner_span_moves_core_quotient
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hn : ¬ V ≤ twoCoreIn Mc) :
    ¬ ⁅twoCoreIn Mc, partnerSpan H Mc⁆ ≤ centralInvolutions T := by
  intro hc
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  let Z := (centralInvolutions T).subgroupOf Mc
  let : Z.Normal := source_chosen_seed_normal h hMc
  let q := QuotientGroup.mk' Z
  have hic : ⁅(partnerSpan H Mc).subgroupOf Mc,pCore 2 Mc⁆ ≤ Z := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator,map_subgroupOf_eq_of_le hKM,commutator_comm]
    exact hc
  have hmap : ⁅((partnerSpan H Mc).subgroupOf Mc).map q,(pCore 2 Mc).map q⁆ = ⊥ := by
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q,QuotientGroup.ker_mk'] using hic
  have hm := map_mono (f := Mc.subtype) (map_le_iff_le_comap.mp
    (commutator_eq_bot_iff_le_centralizer.mp hmap))
  rw [map_subgroupOf_eq_of_le hKM] at hm
  have hKQ := hm.trans (source_chosen_core_quotient_centralizer h hg hMc)
  apply source_chosen_noncore_commutator_not_le h hg hquotient hres hn
  have hVK : V ≤ normalizer (partnerSpan H Mc : Set G) :=
    ((h.prepared.inside_core H hg.outside).trans ((twoCore_le H).trans hg.in_partner)).trans
      (le_normalizer_conjugateSpanBy _ _)
  exact (le_normalizer_iff_commutator_le_left.mp hVK).trans hKQ

/-- A V-moved chief section with both endpoints normal in the original L. -/
theorem source_chosen_partner_moved_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ B U : NormalNode L,
      centralInvolutions T ≤ B.val.map L.subtype ∧ B ⋖ U ∧
      U.val.map L.subtype ≤ twoCoreIn Mc ∧
      ∃ a : L, (a : G) ∈ V ∧ sectionAction B U a ≠ 1 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  have hTM : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  have hTH : (T : Subgroup G) ≤ H := hg.outside.1.1.2
  have hVT : V ≤ (T : Subgroup G) := by
    have hh : twoCoreIn H ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,pCoreIn,twoCoreIn] using
        pCoreIn_le_sylow H (T.subtype hTH)
    exact (h.prepared.inside_core H hg.outside).trans hh
  have hVL : V ≤ L := hVT.trans le_sup_right
  have hZL : centralInvolutions T ≤ L := (centralInvolutions_le_sylow T).trans le_sup_right
  have hQT : twoCoreIn Mc ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,pCoreIn,twoCoreIn] using
      pCoreIn_le_sylow Mc (T.subtype hTM)
  have hQL : twoCoreIn Mc ≤ L := hQT.trans le_sup_right
  have hLQ : L ≤ normalizer (twoCoreIn Mc : Set G) := hLM.trans (by
    simpa only [twoCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 Mc).le_normalizer_map Mc.subtype)
  let Z : NormalNode L := ⟨(centralInvolutions T).subgroupOf L,
    normal_subgroupOf_of_le_normalizer
      (hLM.trans (hMc.le.trans (Subgroup.centralizer_le_normalizer _)))⟩
  let Q : NormalNode L := ⟨(twoCoreIn Mc).subgroupOf L,
    normal_subgroupOf_of_le_normalizer hLQ⟩
  let K : NormalNode L := ⟨(partnerSpan H Mc).subgroupOf L,
    normal_subgroupOf_of_le_normalizer (hLM.trans (le_normalizer_conjugateSpanBy _ _))⟩
  have hK : IsPPerfect 2 K.val := by
    have he : (partnerSpan H Mc).subgroupOf Mc = primeToResidual 3 Mc := by
      rw [hres,threePrimeResidual_eq]
      exact comap_map_eq_self_of_injective Mc.subtype_injective _
    have hp : IsPPerfect 2 ((partnerSpan H Mc).subgroupOf Mc) := by
      rw [he]
      exact isPPerfect_primeToResidual 3 2 (by decide)
    have hp' : IsPPerfect 2 (partnerSpan H Mc) := hp.of_surjective
      (subgroupOfEquivOfLe hKM).toMonoidHom (subgroupOfEquivOfLe hKM).surjective
    exact hp'.of_surjective (subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)).symm.surjective
  have hmove : ¬ ⁅Q.val,K.val⁆ ≤ Z.val := by
    intro hh
    apply source_chosen_partner_span_moves_core_quotient h hg hMc hquotient hres hn
    have hm := map_mono (f := L.subtype) hh
    simpa only [Q,K,Z,map_commutator, map_subgroupOf_eq_of_le hQL,
      map_subgroupOf_eq_of_le (show partnerSpan H Mc ≤ L from le_sup_left),
      map_subgroupOf_eq_of_le hZL] using hm
  have hgen : ⁅K.val,V.subgroupOf L⁆ = K.val := by
    apply map_injective L.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVL,
      map_subgroupOf_eq_of_le (show partnerSpan H Mc ≤ L from le_sup_left)]
    exact (source_chosen_noncore_eq_commutator h hg hquotient hres hs hn).symm
  obtain ⟨B,U,hZB,hBU,hUQ,a,ha⟩ := exists_moved_chief_of_residual_commutator Z Q K
    (V.subgroupOf L) (comap_mono (source_chosen_seed_le_partner_twoCore h hg hMc))
    ((isPGroup_pCoreIn 2 Mc).comap_subtype) hK hmove hgen
  refine ⟨B,U,?_,hBU,?_,a.val,a.property,ha⟩
  · have hm := map_mono (f := L.subtype) hZB
    rwa [map_subgroupOf_eq_of_le hZL] at hm
  · simpa only [Q,map_subgroupOf_eq_of_le hQL] using (map_mono (f := L.subtype) hUQ)

/-- Construct the actual irreducible binary chief action and descend it through
the two-core. The specified involution is nontrivial both in the quotient
group and on this section, with displacement rank between one and two. -/
theorem source_chosen_partner_chief_action
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        IsIrreducible σ ∧
        σ.comp (QuotientGroup.mk' (pCore 2 L)) = binarySectionRepresentation B U ∧
        ∃ a : L, (a : G) ∈ V ∧
          orderOf (QuotientGroup.mk' (pCore 2 L) a) = 2 ∧
          1 ≤ Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ∧
          Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ≤ 2 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨B,U,hB,hc,hU,a,ha,hm⟩ :=
    source_chosen_partner_moved_chief h hg hMc hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  dsimp only
  let ρ := binarySectionRepresentation B U
  let : IsIrreducible ρ := binarySection_irreducible B U hc
  have hk : pCore 2 L ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 L) hk
  let q := QuotientGroup.mk' (pCore 2 L)
  have hmove : ρ a ≠ 1 := by
    intro he
    apply hm
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul x))
  have hqm : q a ≠ 1 := by
    intro he
    apply hmove
    change σ (q a) = 1
    rw [he,map_one]
  have ha2 : a^2=1 := by
    let := h.prepared.elementary
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (a : G) ha)
  have hq2 : orderOf (q a) = 2 := orderOf_eq_prime (by rw [←map_pow,ha2,map_one]) hqm
  have hpos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - (1 : Module.End (ZMod 2) (Additive (Section B U))))) := by
    by_contra hh
    have hz : Module.finrank (ZMod 2) (LinearMap.range (ρ a - (1 : Module.End (ZMod 2) (Additive (Section B U))))) = 0 := by omega
    exact hmove (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  have hbound := source_chosen_partner_section_displacement_le_two h hg hMc hZ hn
    (ambientBinarySection L B U hc.le) hU hB a ha
  exact ⟨σ,(quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance,rfl,a,ha,hq2,hpos,hbound⟩

/-- The image of V on any literal partner section is elementary and quadratic,
and is normalized by the actual image of T. -/
theorem source_chosen_partner_section_actor
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hTL : (T : Subgroup G) ≤ L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W)
    (d : BinaryConjugationSection L U B ρ) (hU : U ≤ twoCoreIn Mc) :
    let τ := BinaryOffender.imageRepresentation ρ
    let f := BinaryOffender.actionHom ρ
    let A := (V.subgroupOf L).map f
    IsElementaryAbelian 2 A ∧ BinaryOffender.IsQuadratic τ A ∧
      ∃ S : Sylow 2 (BinaryOffender.actionImage ρ),
        (S : Subgroup (BinaryOffender.actionImage ρ)) =
          ((T : Subgroup G).subgroupOf L).map f ∧
        A ≤ (S : Subgroup (BinaryOffender.actionImage ρ)) ∧
        (S : Subgroup (BinaryOffender.actionImage ρ)) ≤
          normalizer (A : Set (BinaryOffender.actionImage ρ)) := by
  dsimp only
  let τ := BinaryOffender.imageRepresentation ρ
  let f := BinaryOffender.actionHom ρ
  let A := (V.subgroupOf L).map f
  let := h.prepared.elementary
  have hTH : (T : Subgroup G) ≤ H := hg.outside.1.1.2
  have hQT : twoCoreIn H ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,pCoreIn,twoCoreIn] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hVT : V ≤ (T : Subgroup G) := (h.prepared.inside_core H hg.outside).trans hQT
  have hVL : V ≤ L := hVT.trans hTL
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hcomm : ⁅V,U⁆ ≤ V :=
    ((commutator_mono le_rfl hU).trans
      (source_chosen_partner_core_commutator_le h hg)).trans inf_le_left
  have hc2 : ⁅V,⁅V,U⁆⁆ ≤ B :=
    (commutator_mono le_rfl hcomm).trans
      ((commutator_eq_bot_iff_le_centralizer.mpr V.le_centralizer).le.trans bot_le)
  have hquad : BinaryOffender.IsQuadratic τ A :=
    BinaryConjugationSection.isQuadratic_of_triple_commutator_le L U B V τ f d hc2
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  let S : Sylow 2 (BinaryOffender.actionImage ρ) :=
    (T.subtype hTL).mapSurjective (f := f) hf
  have hAS : A ≤ (S : Subgroup (BinaryOffender.actionImage ρ)) := by
    change (V.subgroupOf L).map f ≤ ((T : Subgroup G).subgroupOf L).map f
    exact map_mono (comap_mono hVT)
  have hnorm : (T : Subgroup G).subgroupOf L ≤ normalizer (V.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq hVL]
    exact comap_mono (h.maximal.1.2.trans h.prepared.normalized)
  have hSA : (S : Subgroup (BinaryOffender.actionImage ρ)) ≤
      normalizer (A : Set (BinaryOffender.actionImage ρ)) := by
    change ((T : Subgroup G).subgroupOf L).map f ≤
      normalizer ((V.subgroupOf L).map f : Set (BinaryOffender.actionImage ρ))
    exact (map_mono hnorm).trans ((V.subgroupOf L).le_normalizer_map f)
  exact ⟨hA,hquad,S,rfl,hAS,hSA⟩

/-- The properties of the literal faithful image needed before recognition.
This is an output predicate; the theorem below constructs it from the source. -/
@[expose] def PartnerChiefImageProperties
    (T : Sylow 2 G) (V L : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W) : Prop :=
  let τ := BinaryOffender.imageRepresentation ρ
  let f := BinaryOffender.actionHom ρ
  let A := (V.subgroupOf L).map f
  Function.Injective τ ∧ IsIrreducible τ ∧
  IsElementaryAbelian 2 A ∧ A ≠ ⊥ ∧ BinaryOffender.IsQuadratic τ A ∧
  ∃ S : Sylow 2 (BinaryOffender.actionImage ρ),
    (S : Subgroup (BinaryOffender.actionImage ρ)) =
      ((T : Subgroup G).subgroupOf L).map f ∧
    A ≤ (S : Subgroup (BinaryOffender.actionImage ρ)) ∧
    (S : Subgroup (BinaryOffender.actionImage ρ)) ≤
      normalizer (A : Set (BinaryOffender.actionImage ρ)) ∧
    ∃ a : L, (a : G) ∈ V ∧ orderOf (f a) = 2 ∧
      1 ≤ Module.finrank (ZMod 2) (LinearMap.range (τ (f a) - 1)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (τ (f a) - 1)) ≤ 2 ∧
      BinaryOffender.quadraticRatio τ ≤ 2

private theorem partner_section_image_properties
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    (hTL : (T : Subgroup G) ≤ L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W)
    (d : BinaryConjugationSection L U B ρ)
    (hU : U ≤ twoCoreIn Mc) (hB : centralInvolutions T ≤ B)
    (hi : IsIrreducible ρ) (a : L) (ha : (a : G) ∈ V) (hm : ρ a ≠ 1) :
    PartnerChiefImageProperties T V L ρ := by
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  obtain ⟨hfaith,hirr,ht,hbound,hq⟩ :=
    source_chosen_partner_section_image_involution h hg hMc hZ hn d hU hB hi a ha hm
  obtain ⟨hA,hquad,S,hS,hAS,hSA⟩ :=
    source_chosen_partner_section_actor h hg hTL ρ d hU
  have hAn : (V.subgroupOf L).map (BinaryOffender.actionHom ρ) ≠ ⊥ := by
    intro he
    have hf : BinaryOffender.actionHom ρ a = 1 := by
      simpa only [he,mem_bot] using (mem_map_of_mem (BinaryOffender.actionHom ρ) ha :
        BinaryOffender.actionHom ρ a ∈ (V.subgroupOf L).map (BinaryOffender.actionHom ρ))
    apply hm
    simpa only [BinaryOffender.imageRepresentation_actionHom,map_one] using
      congrArg (BinaryOffender.imageRepresentation ρ) hf
  have hpos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) := by
    by_contra hh
    have hz : Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) = 0 := by omega
    exact hm (sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  exact ⟨hfaith,hirr,hA,hAn,hquad,S,hS,hAS,hSA,a,ha,ht,hpos,hbound,hq⟩

/-- Construct the actual faithful irreducible chief image, with the source
elementary actor normal in the marked Sylow image and a small involution. -/
theorem source_chosen_partner_faithful_chief_image
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      PartnerChiefImageProperties T V L (binarySectionRepresentation B U) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨B,U,hB,hc,hU,a,ha,hm⟩ :=
    source_chosen_partner_moved_chief h hg hMc hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  dsimp only
  have hmove : binarySectionRepresentation B U a ≠ 1 := by
    intro he
    apply hm
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul x))
  exact partner_section_image_properties h hg hMc hZ hn le_sup_right
    (binarySectionRepresentation B U) (ambientBinarySection L B U hc.le) hU hB
    (binarySection_irreducible B U hc) a ha hmove

end CFSG.Quasithin.Chapter15.Section02
