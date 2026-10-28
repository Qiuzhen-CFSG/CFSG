module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceCubicExclusion
public import Theory.SpecificGroups.Triality.CComponentResidual

/-!
# The triality row of the original Case-I cubic exclusion

The source15.1.22(4) triality row has an outer automorphism of order three,
so the outer-two Facts interface does not apply. The genuine fixed-nine
argument instead identifies the original C-component with O^{3′}(G₁).
The same argument in N_G(V₁) proves that the exchanged moving plane cannot
centralize L. The actual Nine consumer constructs its marker, both planes,
and the moving residual and excludes equality of the two source centralizers.

The quotient is the literal L/O₂(L), and no replacement component or actor
is chosen. Recognizing this quotient and proving the source15.1.22 row's
centralizer equality remain with the source catalogue. The earlier15.1.14
residual centralization is retained at its original boundary.

Source: Aschbacher--Smith15.1.22(4),15.1.25(1),(3),15.1.26,
printed pp.1098,1102, using A.3.18.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source triality row needs its cubic-actor argument: the quotient's
outer group has an actual element of order three. -/
theorem CaseIComponentData.triality_not_binary_facts
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V)
    (e : (d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    ¬ Theory.SpecificGroups.BinaryComponentResidual.Facts (d.L ⧸ pCore 2 d.L) := by
  intro hf
  exact Triality.Standard.binaryCarrier_outer_not_two 1 Nat.zero_lt_one
    (hf.2.2.of_equiv (MulAut.outerCongr e))

/-- The actual triality quotient identifies L and its original cubic actor. -/
theorem CaseIComponentData.source_triality_cubic_component
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)]
    (e : (d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :
    d.L = (primeToResidual 3 d.G1).map d.G1.subtype ∧
      (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype =
        (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype := by
  let := h.elementary
  have hZp : IsPGroup 2 d.Z1 :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)
  have hrG : primeRank 3 d.G1 ≤ 2 :=
    (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot hZp).stronglyQuasithin 3 Nat.prime_three (by decide)
  let K := d.L.subgroupOf d.G1
  let a : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let b : (K ⧸ pCore 2 K) ≃* (d.L ⧸ pCore 2 d.L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv b.symm
  have he := Triality.Standard.cComponent_eq_primeToResidual_three
    d.L_isCComponent_in_G1 hrG 1 Nat.zero_lt_one (b.trans e)
  have hLres : d.L = (primeToResidual 3 d.G1).map d.G1.subtype := by
    have hh := congrArg (map d.G1.subtype) he
    rwa [map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hh
  refine ⟨hLres,?_⟩
  have hh := embedded_primeToResidual_intersection 3 d.G1 M
  rw [←hLres,inf_comm d.L M,inf_comm d.G1 M] at hh
  exact hh.symm

/-- An exchanged moved plane supplies the noncentrality in original 15.1.25(3).
The ambient rank bound is derived in its literal two-local normalizer. -/
theorem CaseIComponentData.fixed_plane_not_centralizes_of_triality
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)]
    (j : (d.L ⧸ pCore 2 d.L) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)
    (V1 V2 Y : Subgroup G) (hZ : d.Z1 ≤ V1)
    (hV1 : IsPGroup 2 V1) (hV2 : V2 ≠ ⊥)
    (hY : (primeToResidual 3 Y).map Y.subtype = Y)
    (hmove : ⁅V2,Y⁆ = V2) (t : G)
    (ht : V2.map (MulAut.conj t).toMonoidHom = V1) :
    ¬ V1 ≤ centralizer (d.L : Set G) := by
  let e := (MulAut.conj t).toMonoidHom
  let A := Y.map e
  have hV1ne : V1 ≠ ⊥ := by
    intro he
    exact hV2 ((map_eq_bot_iff_of_injective V2 (MulAut.conj t).injective).mp (ht.trans he))
  have hAn : A ≤ normalizer (V1 : Set G) := by
    have hn : Y ≤ normalizer (V2 : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr hmove.le
    have hh := map_mono (f := e) hn
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective,ht] at hh
    exact hh
  have hAid : (primeToResidual 3 A).map A.subtype = A := by
    rw [← map_embedded_primeToResidual_of_hom 3 Y e,hY]
  have hAmove : ⁅V1,A⁆ ≠ ⊥ := by
    have he := congrArg (map e) hmove
    rw [map_commutator,ht] at he
    exact fun hz => hV1ne (he.symm.trans hz)
  have hN : primeRank 3 (normalizer (V1 : Set G)) ≤ 2 :=
    (hG.twoLocal_sqtk ⟨V1,hV1ne,hV1,rfl⟩).stronglyQuasithin 3 Nat.prime_three (by decide)
  intro hc
  exact Triality.Standard.cComponent_not_centralizes_of_cubic_movement
    d.L_isCComponent_in_G1 (centralizer_le hZ) 1 Nat.zero_lt_one j hN hAn hAid hAmove
    (le_centralizer_iff.mp hc)

/-- The actual Nine component cannot satisfy the source22 equal-centralizer
conclusion in the triality row. All plane and residual inputs are constructed. -/
theorem PreparedChosenModule.source_caseI_nine_triality_no_equal_centralizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      (Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
          Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) →
        d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
          (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G)) := by
  let := h.elementary
  obtain ⟨v,K,hv,hfixed,hK,hgen,hcard,hSyl,hbound⟩ :=
    chosen_nine_marked_image_with_movement T hM.1.2 h.normalized h9
  obtain ⟨d,hdZ,hdrow,hdcard,hodd,hq,hL,hSL,hV2,hn,hmove⟩ :=
    h.caseI_component_of_marked_image hG T hempty hM hmany hJ hu hne hfull h9 hres
      v K hv hfixed hK hgen hcard hSyl hbound
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let V1 := V ⊓ centralizer (R : Set G)
  let V2 := ⁅V,R⁆
  let Y := (primeToResidual 3 C).map C.subtype
  have hC : C = M ⊓ centralizer (zpowers (v.toMul : G) : Set G) := by
    change M ⊓ centralizer (d.Z1 : Set G) = _
    rw [hdZ]
  have hplanes : Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧
      V1 ⊓ V2 = ⊥ ∧ d.Z1 ≤ V1 := by
    let P (Z : Subgroup G) : Prop :=
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) = 4 ∧ Nat.card (⁅V,R⁆ : Subgroup G) = 4 ∧
        (V ⊓ centralizer (R : Set G)) ⊔ ⁅V,R⁆ = V ∧
        (V ⊓ centralizer (R : Set G)) ⊓ ⁅V,R⁆ = ⊥ ∧
        Z ≤ V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := source_nine_planes T h.normalized h9 v K hv hK hcard
    exact (congrArg P hdZ).mpr hp
  have haction : d.S.relIndex (T : Subgroup G) = 2 ∧
      ∀ t ∈ (T : Subgroup G), t ∉ d.S →
        V2.map (MulAut.conj t).toMonoidHom = V1 := by
    let P (Z : Subgroup G) : Prop :=
      let S := (T : Subgroup G) ⊓ centralizer (Z : Set G)
      let R := (pResidual 2 (M ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z : Set G)).subtype
      S.relIndex (T : Subgroup G) = 2 ∧
        ∀ t ∈ (T : Subgroup G), t ∉ S →
          ⁅V,R⁆.map (MulAut.conj t).toMonoidHom = V ⊓ centralizer (R : Set G)
    have hp : P (zpowers (v.toMul : G)) := by
      obtain ⟨hi,_,_,_,he⟩ := source_nine_plane_action T hM.1.2 h.normalized h9 v K hv hK hcard hSyl
      exact ⟨hi,fun t ht hs => (he t ht hs).2⟩
    exact (congrArg P hdZ).mpr hp
  refine ⟨d,hdrow,hdcard,hodd,hq,hL,hSL,?_⟩
  rintro ⟨j⟩ heq
  let := hq
  have hV2ne : V2 ≠ ⊥ := by
    intro he
    have hc := hplanes.2.1
    rw [he,card_bot] at hc
    omega
  have hYid : (primeToResidual 3 Y).map Y.subtype = Y := by
    rw [←map_embedded_primeToResidual_of_hom 3 (primeToResidual 3 C) C.subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 C) le_rfl]
  have he : ⁅V,Y⁆ = V2 := by
    dsimp only [Y,V2,R]
    rw [hC]
    exact marked_primeToResidual_commutator M V h.normalized v K hK hcard
  have hYp : IsPPerfect 2 Y := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
    ((primeToResidual 3 C).equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hYV : Y ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  have hV2Y : ⁅V2,Y⁆ = V2 := by
    rw [←he]
    exact commutator_isPPerfect_idempotent Y V hYp (IsElementaryAbelian.isPGroup 2 V) hYV
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ d.S := by
    by_contra! hh
    have he := relIndex_eq_one.mpr hh
    rw [haction.1] at he
    contradiction
  have hnon := d.fixed_plane_not_centralizes_of_triality hG j V1 V2 Y hplanes.2.2.2.2
    ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left) hV2ne hYid hV2Y t
    (haction.2 t ht htS)
  have hY := (d.source_triality_cubic_component hG h j).2
  have hYR : Y ≤ R := map_mono (le_pResidual_of_isPPerfect _
    (isPPerfect_primeToResidual 3 2 (by decide)))
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hV1SY : V1 ≤ d.S ⊓ centralizer (Y : Set G) :=
    le_inf (le_inf (inf_le_left.trans hVT)
      (inf_le_left.trans (V.le_centralizer.trans
        (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
      (inf_le_right.trans (centralizer_le hYR))
  have heq' : d.S ⊓ centralizer (Y : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
    change d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype) : Set G) = _
    rw [hY]
    exact heq
  exact hnon ((hV1SY.trans heq'.le).trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section01
