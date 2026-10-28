module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Qrc.Primewise
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Radical.Inversion
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
public import Theory.GroupTheory.Fitting.OmegaIntersection

/-!
# Two-closedness of the actual comparison radical

Transport the primewise intersection from Ξₚ(L) to the literal
Ω₁(Oₚ(L/O₂(L))) using the original inclusion and quotient maps.
Its Frattini subgroup is cyclic. Perfectness centralizes this
characteristic subgroup. For an abelian prime core, the intersection
is trivial by Cauchy's theorem; for an exponent-p core it is central.
The nilpotent decomposition therefore makes the entire Fitting
intersection central, retaining all higher homocyclic exponents.

The radical has index two over that Fitting subgroup. A central kernel
lifts its normal Sylow two-subgroup, and the original O₂(L) kernel lifts
it again. Thus H∩O∞(L) is two-closed. No center–Frattini equality is used.
Canonical starred membership is the earlier source premise owned by
qt-d-1314-canonical-radical-star and discharged by qt-d-1317-source.

Source: Aschbacher--Smith 13.1.9, case (I), printed p.869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

theorem comparison_omega_frattini
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ((H.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))) ⊓
      omegaCore p (XiQuotient L) ≤
      (frattini (omegaCore p (XiQuotient L))).map (omegaCore p (XiQuotient L)).subtype := by
  let q := QuotientGroup.mk' (pCore 2 L)
  let X := XiP p L
  let D := H.subgroupOf L
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hcore : q.ker ≤ D := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hpc := pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer hTL) (mem_map_of_mem L.subtype hx)
    have hst := pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤
      L ⊔ (T : Subgroup G) from le_sup_right)] at hst
    exact hH.1.1.2 (hst hpc)
  have himage : (X.subgroupOf L).map q = omegaCore p (XiQuotient L) := by
    rw [XiP_subgroupOf]
    exact xiPIn_map_quotient ho L
  nth_rw 1 [← himage]
  rw [inf_comm,← map_inf_of_ker_le q _ D hcore]
  rintro z ⟨x,⟨hxX,hxH⟩,rfl⟩
  have hxG : (x : G) ∈ H ⊓ X := ⟨hxH,hxX⟩
  obtain ⟨a,ha,he⟩ := comparison_inf_radical_le_frattini h hmany hs hL hn hH ho hd hxG
  have hax : inclusion (XiP_le p L) a = x := Subtype.ext he
  let e := xiPQuotientEquivCore ho L
  have haPhi : e (QuotientGroup.mk' (pCore 2 X) a) ∈ frattini (omegaCore p (XiQuotient L)) := by
    rw [← frattini_map_equiv e]
    exact mem_map_of_mem e.toMonoidHom ha
  refine ⟨e (QuotientGroup.mk' (pCore 2 X) a),haPhi,?_⟩
  exact (xiPQuotientEquivCore_apply_mk ho L a).trans (congrArg q hax)

private theorem odd_frattini_isCyclic {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (hQ : XiOddQuotient p Q) : IsCyclic (frattini Q) := by
  rcases hQ with ⟨hE, _⟩ | ⟨hE, _, _⟩
  · let := hE
    let : Fact (IsPGroup p Q) := ⟨IsElementaryAbelian.isPGroup p Q⟩
    rw [frattini_eq_bot_of_isElementaryAbelian (R := Q) (p := p)]
    infer_instance
  · let := hE.quotient_elementary_abelian
    let : Fact (IsPGroup p (Q ⧸ center Q)) := ⟨IsElementaryAbelian.isPGroup p _⟩
    have hphi : frattini Q ≤ center Q := by
      have hh := frattini_le_comap_frattini_of_surjective
        (QuotientGroup.mk'_surjective (center Q))
      rw [frattini_eq_bot_of_isElementaryAbelian (R := Q ⧸ center Q) (p := p),
        MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hh
      exact hh
    let : IsCyclic (center Q) := isCyclic_of_prime_card hE.center_order_p
    exact isCyclic_of_injective (inclusion hphi) (inclusion_injective hphi)

private theorem source_core_shape (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    IsMulCommutative (pCore p (XiQuotient L)) ∨
      ∀ x : pCore p (XiQuotient L), x ^ p = 1 := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  let C := radicalLocalImage T L
  let e : XiQuotient L ≃* C := radicalLocalQuotientEquiv hL.1.1
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hL.1.1.1
  have hdC : p ∣ Nat.card (fittingSubgroup C) := by
    rw [← map_fitting_equiv e,card_map_of_injective e.injective]
    exact hd
  let ep : pCore p (XiQuotient L) ≃* pCore p C :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso p e))
  rcases RadicalStructure.core_shape
    (RadicalStructure.nonsimple_radical hc (fun hs => hn (hs.of_mulEquiv e.symm))) hdC
      with hab | hexp
  · let := hab
    exact Or.inl (IsMulCommutative.of_comm (fun x y => ep.injective
      (by simp only [map_mul]; exact mul_comm' _ _)))
  · exact Or.inr (fun x => ep.injective (by
      simpa only [map_pow,map_one] using hexp (ep x)))

theorem comparison_fitting_intersection_le_center
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ((H.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))) ⊓
      fittingSubgroup (XiQuotient L) ≤ center (XiQuotient L) := by
  let K := XiQuotient L
  let D := (H.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))
  let : Group.IsPerfect L := mem_L_isPerfect hL.1.1
  let : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  apply inf_fitting_le_center_of_prime_intersections D
  intro p hp hd
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := Nat.coprime_two_left.mp
    ((local_fitting_odd_source h hL).of_dvd_right hd)
  let W := omega (pCore p K) (p := p) 1
  let e : W ≃* omegaCore p K := W.equivMapOfInjective
    (pCore p K).subtype (pCore p K).subtype_injective
  obtain ⟨r,hr,_,hq⟩ := (hs L hL hn p hp ho hd).1.odd_quotient
  let : Fact r.Prime := ⟨hr⟩
  have hw : XiOddQuotient r W :=
    hq.of_mulEquiv ((xiPQuotientEquivCore ho L).trans e.symm)
  apply inf_le_center_of_omega_frattini D (pCore p K) pCore_isPGroup
    (source_core_shape h hL hn hd) (odd_frattini_isCyclic hw)
  have he : ((frattini W).map W.subtype).map (pCore p K).subtype =
      (frattini (omegaCore p K)).map (omegaCore p K).subtype := by
    rw [map_map,show (pCore p K).subtype.comp W.subtype =
      (omegaCore p K).subtype.comp e.toMonoidHom from rfl,← map_map,frattini_map_equiv]
  rw [he]
  exact comparison_omega_frattini h hmany hs hL hn hH ho hd

theorem comparison_radical_image_twoClosed
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Odd (pCore 2 ((((H.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))) ⊓
      solvableRadical (XiQuotient L) : Subgroup (XiQuotient L)))).index := by
  let K := XiQuotient L
  let D := (H.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))
  let E := D ⊓ solvableRadical K
  let q := QuotientGroup.mk' (fittingSubgroup K)
  let f := q.comp E.subtype
  have himage : IsPGroup 2 f.range := by
    have hcard : Nat.card ((solvableRadical K).map q) = 2 := by
      rw [← relIndex_ker,QuotientGroup.ker_mk']
      exact radical_fitting_index_source h hL hn
    have hr : f.range ≤ (solvableRadical K).map q := by
      rw [MonoidHom.range_comp,range_subtype]
      exact map_mono inf_le_right
    exact (IsPGroup.of_card (p := 2) (n := 1) (by simpa only [pow_one] using hcard)).to_le hr
  have hcentral : f.rangeRestrict.ker ≤ center E := by
    intro x hx
    have hxf : (x : K) ∈ fittingSubgroup K :=
      (QuotientGroup.eq_one_iff (x : K)).mp (congrArg Subtype.val hx)
    have hxZ := comparison_fitting_intersection_le_center h hmany hs hL hn hH
      ⟨x.property.1,hxf⟩
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hxZ y))
  have htop : pCore 2 f.range = ⊤ := top_unique
    (le_sSup ⟨inferInstance,himage.to_subgroup ⊤⟩)
  exact OddHall.odd_pCore_index_of_surjective_central_kernel f.rangeRestrict
    f.rangeRestrict_surjective hcentral (by rw [htop,index_top]; decide)

theorem comparison_radical_twoClosed
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : Escape.CanonicalStars T) {L H : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Odd (pCore 2 (H ⊓ (solvableRadical L).map L.subtype : Subgroup G)).index := by
  let K := XiQuotient L
  let q := QuotientGroup.mk' (pCore 2 L)
  let A := H ⊓ (solvableRadical L).map L.subtype
  let B := (H.subgroupOf L) ⊓ solvableRadical L
  let E := ((H.subgroupOf L).map q) ⊓ solvableRadical K
  have hAL : A ≤ L := inf_le_right.trans (map_subtype_le _)
  have hB : A.subgroupOf L = B := by
    change (H ⊓ (solvableRadical L).map L.subtype).comap L.subtype = _
    rw [comap_inf,comap_map_eq_self_of_injective L.subtype_injective]
    rfl
  let e : B ≃* A := (MulEquiv.subgroupCongr hB).symm.trans (subgroupOfEquivOfLe hAL)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    infer_instance
  have hrad : (solvableRadical L).map q = solvableRadical K := by
    rw [← comap_solvableRadical_eq_of_solvable_ker q (QuotientGroup.mk'_surjective _),
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hkerR : q.ker ≤ solvableRadical L :=
    le_solvableRadical q.ker inferInstance inferInstance
  have hBE : B.map q = E := by
    rw [map_inf_of_ker_le q _ _ hkerR,hrad]
  let f : B →* E := (MulEquiv.subgroupCongr hBE).toMonoidHom.comp (q.subgroupMap B)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hBE).surjective.comp (q.subgroupMap_surjective B)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 L).comap B.subtype := by
      rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hBE).injective,
        ker_subgroupMap,QuotientGroup.ker_mk']
      rfl
    rw [he]
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  have hi : Odd (pCore 2 B).index := odd_pCore_index_of_surjective_two_kernel f hf hk
    (comparison_radical_image_twoClosed h hmany hs hL hn hH)
  rw [← pCore_map_iso 2 e]
  rwa [index_map_of_bijective e.bijective]


end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
