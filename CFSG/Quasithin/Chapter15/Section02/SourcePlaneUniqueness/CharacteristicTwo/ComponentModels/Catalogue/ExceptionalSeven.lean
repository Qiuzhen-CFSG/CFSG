module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.TripleSix
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSevenNormalizer
public import Theory.Representation.BinaryAlternatingSevenControl.PointStabilizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Recognition.Original

/-!
# Excluding the exceptional A₇ row on the original component

Inner radical action fixes the center of X/O₂(X), so its full preimage
normalizes R and lies in the original NI by C.2.3 normalizer control.
A cubic center would meet the rank-two residual K nontrivially, contrary
to K∩M = O₂(K). The center is therefore trivial, and the literal core-to-star
map identifies the full original core quotient with A₇.

The original U is contained in the actual star moved subgroup. Its seed
U∩ZS has a vector surviving the moved central quotient, by the original
seed centralizer identity. K fixes this vector, but its E₉ subgroup maps
injectively into the vector stabilizer in A₇, of order 168: a contradiction.

Source: Aschbacher--Smith 15.2.23, printed pp.1116--1117, using C.2.3
and the exceptional four-dimensional A₇ action of C.2.7.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding PlaneUniquenessPreceding.LinearThree TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {I X R N : Subgroup G}

omit [Finite G] in
private theorem central_core_preimage_normalizes_of_inner
    (hR : R ≤ normalizer (X : Set G))
    (hQ : X.pCoreIn 2 ≤ R)
    (hi : ∀ r : R, pCoreNormalizerAction 2 X (inclusion hR r) ∈
      MulAut.innerSubgroup (X ⧸ pCore 2 X)) :
    centralCorePreimage X ≤ normalizer (R : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  apply le_trans (commutator_le.mpr ?_) hQ
  intro r hr c hc
  obtain ⟨x,hx,rfl⟩ := hc
  obtain ⟨z,hz⟩ := hi ⟨r,hr⟩
  have hfix : pCoreNormalizerAction 2 X (inclusion hR ⟨r,hr⟩)
      (QuotientGroup.mk' (pCore 2 X) x) = QuotientGroup.mk' (pCore 2 X) x := by
    rw [←hz]
    change z * QuotientGroup.mk' (pCore 2 X) x * z⁻¹ = _
    rw [mem_center_iff.mp hx z, mul_inv_cancel_right]
  have hmem : X.normalizerMonoidHom (inclusion hR ⟨r,hr⟩) x / x ∈ pCore 2 X :=
    QuotientGroup.eq_iff_div_mem.mp ((pCoreNormalizerAction_mk 2 X _ x).symm.trans hfix)
  refine ⟨_,hmem,?_⟩
  simp only [div_eq_mul_inv, commutatorElement_def]
  rfl

variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include hsource in
/-- Inner radical action places the full central preimage in the original NI. -/
theorem normalized_center_preimage_le_intersection_of_inner
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hi : ∀ r : (M ⊓ I).pCoreIn 2,
      pCoreNormalizerAction 2 X (inclusion s.radical_normalizes r) ∈
        MulAut.innerSubgroup (X ⧸ pCore 2 X)) :
    centralCorePreimage X ≤ M ⊓ I := by
  let R := (M ⊓ I).pCoreIn 2
  let h := normalized_component_input (hsource := hsource) hI hcore s
  let J := X ⊔ R
  let : (X.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer s.radical_normalizes)
  have hQ : X.pCoreIn 2 ≤ R :=
    (pCoreAmbient_mono_of_isSubnormalIn X J 2 le_sup_left
      (source_join_input h).component.2.subnormal).trans
      (source_joinCore_le_radical (source_join_input h))
  have hn := central_core_preimage_normalizes_of_inner s.radical_normalizes hQ hi
  have hN := (normalizer_le_characteristicNormalizerClosure_self
    (R.subgroupOf I) h.setup.radical.1).trans h.setup.characteristic_control
  intro x hx
  have hxI : x ∈ I := s.component.1 (map_subtype_le _ hx)
  apply hN (show (⟨x,hxI⟩ : I) ∈ normalizer (R.subgroupOf I : Set I) from ?_)
  rw [←subgroupOf_normalizer_eq h.setup.radical_le]
  exact hn hx

include d in
/-- The original rank-two residual excludes a cubic core-quotient center. -/
theorem normalized_core_center_card_one_of_inner
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (hi : ∀ r : (M ⊓ I).pCoreIn 2,
      pCoreNormalizerAction 2 X (inclusion s.radical_normalizes r) ∈
        MulAut.innerSubgroup (X ⧸ pCore 2 X)) :
    Nat.card (center (X ⧸ pCore 2 X)) = 1 := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  rcases coreQuotient_center_card_from_source h with hz | hz
  · exact hz
  let K := (pResidual 2 H).map H.subtype
  let C := centralCorePreimage X
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hCI : C ≤ I := (map_subtype_le _).trans s.component.1
  have hCM : C ≤ M :=
    (normalized_center_preimage_le_intersection_of_inner (hsource := hsource) hI hcore s hi).trans inf_le_left
  have hKC : K ≤ normalizer (C : Set G) := s.residual_normalizes.trans
    (normalizer_le_normalizer_characteristic_image X (centralPreimage (pCore 2 X)))
  have hc : 3 ∣ Nat.card C := by
    have hh := (centralPreimage (pCore 2 X)).card_map_dvd (QuotientGroup.mk' (pCore 2 X))
    rw [map_centralPreimage,hz] at hh
    simpa only [C,centralCorePreimage,card_map_of_injective X.subtype_injective] using hh
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hA
  let E := A.map (inclusion hKI)
  let e := A.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hE : Nat.card E = 3^2 := by
    rw [←Nat.card_congr e.toEquiv,hcard,residual_rank_two d]
  have hn : E ≤ normalizer (C.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hCI]
    rintro _ ⟨x,_,rfl⟩
    exact hKC x.property
  have hne := Subgroup.inf_ne_bot_of_elementary_plane E (C.subgroupOf I) hn
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hCI).toEquiv]) hE
    ((Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide))
  have htwo : IsPGroup 2 (K ⊓ C : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rw [←residual_intersection_eq_core d]
    exact inf_le_inf_left K hCM
  have hle : E ⊓ C.subgroupOf I ≤ (K ⊓ C).subgroupOf I := by
    rintro x ⟨⟨k,_,hk⟩,hx⟩
    have hkx : (k : G) = (x : G) := congrArg Subtype.val hk
    refine ⟨?_,hx⟩
    change (x : G) ∈ K
    rw [←hkx]
    exact k.property
  have hdis := (IsElementaryAbelian.isPGroup 3 E).disjoint_of_coprime htwo.comap_subtype
    (by decide : Nat.Coprime 3 2)
  exact (hne (bot_unique ((le_inf inf_le_left hle).trans hdis.eq_bot.le))).elim

include d in
/-- The exceptional moved action identifies the full original core quotient with A₇. -/
theorem normalized_exceptionalSeven_core_model
    (hI : PlaneEscapes Mc ZS I) (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hf : Function.Injective s.action)
    (e : ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    Function.Injective (coreToStar selection.radical_normalizes) ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)) := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hz := normalized_core_center_card_one_of_inner d hI hcore selection
    (fun r => alternatingSeven_four_normalizer_inner h hCJ s hf e hd r
      (selection.radical_normalizes r.property) (((M ⊓ I).pCoreIn 2).le_normalizer r.property))
  have hk : (coreToStar selection.radical_normalizes).ker = ⊥ := by
    apply bot_unique
    exact (coreToStar_ker_central_from_source h).trans_eq ((eq_bot_iff_card _).mpr hz)
  have hinj := (coreToStar selection.radical_normalizes).ker_eq_bot_iff.mp hk
  exact ⟨hinj,⟨(MulEquiv.ofBijective (coreToStar selection.radical_normalizes)
    ⟨hinj,coreToStar_surjective selection.radical_normalizes⟩).trans
      ((subgroupOfEquivOfLe hCJ).symm.trans e)⟩⟩

include d in
/-- The original reduced U lies in the literal star commutator, before any model choice. -/
theorem original_U_le_star_moved
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (h : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X) :
    (U X ZS).subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2) ≤
      ⁅starV X ((M ⊓ I).pCoreIn 2), X.subgroupOf (X ⊔ (M ⊓ I).pCoreIn 2)⁆ := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let W := (U X ZS).subgroupOf J
  have hr := (U_reduced_in_component_radical d hI hfit hXI hn hout h).1
  let := hr.elementary
  have hW : W ≤ starV X R := by
    intro w hw
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hr.le_pCore hw, ?_, hr.le_centralizer_pCore hw⟩
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) (⟨w,hw⟩ : W)
    exact congrArg W.subtype hh
  have hUJ : U X ZS ≤ J := (U_le_intersection_radical d hI hfit hXI).trans le_sup_right
  have hm : ⁅W,X.subgroupOf J⁆ = W := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (show X ≤ J from le_sup_left), U_fully_moved d hI hfit h.component]
  exact hm.symm.le.trans (commutator_mono hW le_rfl)

include d in
/-- The original rank-two K cannot fix the nonzero seed in an exceptional A₇ four-space. -/
theorem normalized_exceptionalSeven_false
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    (hCJ : starImage X ((M ⊓ I).pCoreIn 2) X ≤
      offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))
    (s : MovedSection
      ((starRepresentation X ((M ⊓ I).pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2))).subtype)
      ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
        (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))))
    (hf : Function.Injective s.action)
    (e : ((starImage X ((M ⊓ I).pCoreIn 2) X).subgroupOf
      (offenderSubgroup (starRepresentation X ((M ⊓ I).pCoreIn 2)))) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) : False := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let B := offenderSubgroup (starRepresentation X R)
  let L := (starImage X R X).subgroupOf B
  let η : L ≃* starImage X R X := subgroupOfEquivOfLe hCJ
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  let eA := η.symm.trans e
  let eC := alternatingStarCoreCenterEquiv h (by decide : 5 ≤ 7) eA
  have hzC : Nat.card (center (X ⧸ pCore 2 X)) ≤ 3 := by
    rcases coreQuotient_center_card_from_source h with hc | hc <;> omega
  have hn := alternating_component_normalized (hsource := hsource) hI selection.toSelected
    hzC (Or.inr rfl) eC
  have hout := alternating_star_not_le_partner d horbit hI hcore selection (Or.inr rfl) eA
  have hK := alternating_star_residual_le_M1 d hI hcore selection (Or.inr rfl) eA
  have hseed : ¬ U X ZS ⊓ ZS ≤ centralizer (X : Set G) := by
    intro hh
    apply hout
    have hX : X ≤ M1 X ZS := by
      rw [← U_seed_centralizer d hI hfit selection.component.1 hn]
      exact le_inf le_rfl (le_centralizer_iff.mp hh)
    exact hX.trans ((M1_le_partner_intersection d hI selection.component.1).trans inf_le_left)
  obtain ⟨u,hu,hnc⟩ := SetLike.not_le_iff_exists.mp hseed
  have hUJ : U X ZS ≤ J :=
    (U_le_intersection_radical d hI hfit selection.component.1).trans le_sup_right
  have hm : (⟨u,hUJ hu.1⟩ : J) ∈ ⁅starV X R,X.subgroupOf J⁆ :=
    original_U_le_star_moved d hI hfit selection.component.1 hn hout h hu.1
  let v : Additive (starV X R) :=
    Additive.ofMul ⟨⟨u,hUJ hu.1⟩,commutator_le_left _ _ hm⟩
  have hv : v ∈ s.space.toSubmodule := by
    let : IsElementaryAbelian 2 (⁅starV X R,X.subgroupOf J⁆ : Subgroup J) :=
      IsElementaryAbelian.of_injective (inclusion (commutator_le_left (starV X R) (X.subgroupOf J)))
        (inclusion_injective _)
    rw [s.space_eq]
    change v ∈ subspaceCommutator ((starRepresentation X R).comp B.subtype) ⊤ L
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hCJ]
    change v ∈ subspaceCommutator (starRepresentation X R) ⊤
      ((X.subgroupOf J).map (QuotientGroup.mk' (starKernel X R)))
    exact (NormalElementaryQuotient.movedEquiv (starV X R)
      (QuotientGroup.mk' (starKernel X R)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) (X.subgroupOf J)
      (Additive.ofMul ⟨⟨u,hUJ hu.1⟩,hm⟩)).property
  let z : s.space.toSubmodule ⧸ s.central.toSubmodule := Submodule.Quotient.mk ⟨v,hv⟩
  have hz : z ≠ 0 := by
    intro he
    have hc : (⟨v,hv⟩ : s.space.toSubmodule) ∈ s.central.toSubmodule :=
      by
        change Submodule.Quotient.mk (⟨v,hv⟩ : s.space.toSubmodule) = 0 at he
        simpa only [Submodule.Quotient.mk_eq_zero] using he
    rw [s.central_eq] at hc
    apply hnc
    intro x hx
    have hh := congrArg (fun w : s.space.toSubmodule => ((w.val.toMul : J) : G))
      (hc (η.symm (toStarImage X R ⟨x,hx⟩)))
    change (((starRepresentation X R
      (QuotientGroup.mk' (starKernel X R) (⟨x,mem_sup_left hx⟩ : J)) v).toMul : J) : G) = u at hh
    rw [starRepresentation_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let K := (pResidual 2 H).map H.subtype
  have hKX : K ≤ X := hK.trans inf_le_left
  let f : K →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
    (η.symm.toMonoidHom.comp ((toStarImage X R).comp (inclusion hKX)))
  let σ := (s.action.comp L.subtype).comp e.symm.toMonoidHom
  have hσ : Function.Injective σ := hf.comp (Subtype.val_injective.comp e.symm.injective)
  have hfix (k : K) : σ (f k) z = z := by
    let l : L := η.symm (toStarImage X R (inclusion hKX k))
    change s.central.quotientRepresentation (L.subtype (e.symm (e l))) z = z
    apply (congrArg (fun y : L => s.central.quotientRepresentation (L.subtype y) z)
      (e.symm_apply_apply l)).trans
    change Submodule.Quotient.mk (s.space.toRepresentation
      (L.subtype l) ⟨v,hv⟩) = Submodule.Quotient.mk ⟨v,hv⟩
    congr 1
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (((starRepresentation X R
      (QuotientGroup.mk' (starKernel X R) (⟨k,mem_sup_left (hKX k.property)⟩ : J)) v).toMul : J) : G) = u
    rw [starRepresentation_apply]
    change (k : G) * u * (k : G)⁻¹ = u
    rw [← d.residual_centralizes k.property u hu.2, mul_inv_cancel_right]
  have hi := (normalized_exceptionalSeven_core_model d hI hcore selection hCJ s hf e hd).1
  have hker : IsPGroup 2 f.ker := by
    apply ((pCore_isPGroup (p := 2) (G := X)).comap_of_injective
      (inclusion hKX) (inclusion_injective hKX)).to_le
    intro k hk
    apply (QuotientGroup.eq_one_iff (N := pCore 2 X) (inclusion hKX k)).mp
    apply hi
    change coreToStar selection.radical_normalizes
      (QuotientGroup.mk' (pCore 2 X) (inclusion hKX k)) =
        coreToStar selection.radical_normalizes 1
    rw [map_one, coreToStar_mk]
    apply η.symm.injective
    apply e.injective
    change e (η.symm (toStarImage X R (inclusion hKX k))) = 1 at hk
    simpa only [map_one] using hk
  obtain ⟨A,hA,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hA
  have hdis := (IsElementaryAbelian.isPGroup 3 A).disjoint_of_coprime hker
    (by decide : Nat.Coprime 3 2)
  let fA := f.comp A.subtype
  have hfA : Function.Injective fA := by
    apply (injective_iff_map_eq_one fA).mpr
    intro a ha
    apply Subtype.ext
    exact mem_bot.mp (hdis.eq_bot.le ⟨a.property,ha⟩)
  let t : A →* BinaryAlternatingSevenControl.pointStabilizer σ z :=
    fA.codRestrict _ (fun a => (BinaryAlternatingSevenControl.mem_pointStabilizer σ z (fA a)).mpr (hfix a))
  have ht : Function.Injective t := fun a b hh => hfA (congrArg Subtype.val hh)
  have hdiv := Subgroup.card_dvd_of_injective t ht
  rw [hcard,residual_rank_two d,BinaryAlternatingSevenControl.pointStabilizer_card σ hσ hd hz] at hdiv
  norm_num at hdiv

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
