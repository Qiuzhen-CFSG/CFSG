module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.CoreFour
/-!
# Four-group Sylows in the original prime-core branch

The original dihedral two-core has self-centralizing four-groups. Its
normality and the previously proved Sylow of C_G(t) make that four-group
Sylow in the simultaneous centralizer of t,i,K. The model is the actual
core equivalence supplied by the earlier original prime source theorem.

Source: Aschbacher–Smith 2.5.21, printed p.566.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem model_four_selfcentralizing
    {C : Type*} [Group C]
    (hm : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (C ≃* DihedralGroup (2 ^ k))) ∨
      Nonempty (C ≃* Semidihedral.StandardModel 4 (by decide)))
    (V : Subgroup C) (hV : IsKleinFour V) : centralizer (V : Set C) ≤ V := by
  rcases hm with hm | hm
  · obtain ⟨k,hk,⟨e⟩⟩ := hm
    exact GorensteinWalter.centralizer_kleinFour_le_of_dihedral_mulEquiv (by omega) e V hV
  · obtain ⟨e⟩ := hm
    have hs : Stellmacher.IsSemidihedralGroup C := ABG.semidihedral_equiv e.symm
      ⟨4, by decide, Semidihedral.standardModel_card 4 (by decide),
        Semidihedral.standardRotation 4 (by decide), Semidihedral.standardReflection 4 (by decide),
        Semidihedral.standardRotation_order 4 (by decide),
        Semidihedral.standardReflection_order 4 (by decide),
        Semidihedral.standard_conjugation 4 (by decide),
        Semidihedral.standard_generators 4 (by decide)⟩
    obtain ⟨_,_,_,_,_,_,hall⟩ := ABG.QuasiDihedral.four_quaternion_subgroups hs
    rw [(hall V (Or.inl hV)).1]
    exact map_subtype_le _

omit [Finite G] in
private theorem ambient_four_selfcentralizing
    (C : Subgroup G)
    (hm : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (C ≃* DihedralGroup (2 ^ k))) ∨
      Nonempty (C ≃* Semidihedral.StandardModel 4 (by decide)))
    (V : Subgroup G) (hV : IsKleinFour V) (hVC : V ≤ C) :
    C ⊓ centralizer (V : Set G) ≤ V := by
  let eV := subgroupOfEquivOfLe hVC
  have hVi : IsKleinFour (V.subgroupOf C) := {
    card_four := (Nat.card_congr eV.toEquiv).trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).trans hV.exponent_two }
  intro x hx
  exact model_four_selfcentralizing hm (V.subgroupOf C) hVi
    (show (⟨x,hx.1⟩ : C) ∈ centralizer (V.subgroupOf C : Set C) from
      fun v hv => Subtype.ext (hx.2 v hv))

omit [Finite G] in
private theorem centralizer_core_four
    (C : Subgroup G)
    (hm : (∃ k : ℕ, 2 ≤ k ∧ Nonempty (C ≃* DihedralGroup (2 ^ k))) ∨
      Nonempty (C ≃* Semidihedral.StandardModel 4 (by decide)))
    (t i : G) (ht : orderOf t = 2) (hi : orderOf i = 2) (hti : t ≠ i)
    (htC : t ∈ C) (hiC : i ∈ C) (htZ : t ∈ centralizer (C : Set G)) :
    C ⊓ centralizer ({i} : Set G) = zpowers t ⊔ zpowers i ∧
      IsKleinFour (C ⊓ centralizer ({i} : Set G) : Subgroup G) := by
  let V := closure ({t,i} : Set G)
  have htiC : Commute t i := (htZ i hiC).symm
  have hV : IsKleinFour V := isKleinFour_closure_pair_of_orderOf t i ht hi hti htiC
  have hVC : V ≤ C := (closure_le _).mpr (by rintro a (rfl | rfl) <;> assumption)
  have hRV : C ⊓ centralizer ({i} : Set G) ≤ V := by
    apply le_trans ?_ (ambient_four_selfcentralizing C hm V hV hVC)
    refine le_inf inf_le_left ?_
    intro a ha v hv
    have hVa : V ≤ centralizer ({a} : Set G) := by
      apply (closure_le _).mpr
      rintro x (rfl | rfl)
      · exact mem_centralizer_singleton_iff.mpr (htZ a ha.1).symm
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha.2).symm
    exact mem_centralizer_singleton_iff.mp (hVa hv)
  have hVR : V ≤ C ⊓ centralizer ({i} : Set G) := by
    refine le_inf hVC ((closure_le _).mpr ?_)
    rintro a (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr htiC.eq
    · exact mem_centralizer_singleton_iff.mpr rfl
  have he := le_antisymm hRV hVR
  have hVeq : V = zpowers t ⊔ zpowers i := by
    apply le_antisymm
    · apply (closure_le _).mpr
      have htV : t ∈ zpowers t ⊔ zpowers i :=
        (show zpowers t ≤ zpowers t ⊔ zpowers i from le_sup_left) (mem_zpowers t)
      have hiV : i ∈ zpowers t ⊔ zpowers i :=
        (show zpowers i ≤ zpowers t ⊔ zpowers i from le_sup_right) (mem_zpowers i)
      rintro a (rfl | rfl) <;> assumption
    · exact sup_le (zpowers_le.mpr (subset_closure (by simp)))
        (zpowers_le.mpr (subset_closure (by simp)))
  exact ⟨he.trans hVeq, he.symm ▸ hV⟩

private theorem source_core_sylow_centralizer
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype)) :
    Chapter1.IsSylowIn 2 (twoCore H)
      (centralizer ({t} : Set G) ⊓ centralizer (K : Set G)) := by
  let J := centralizer ({t} : Set G)
  let C := J ⊓ centralizer (K : Set G)
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨hHJ,_,⟨P,hP⟩,_⟩ := MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  have hCJ : C ≤ J := inf_le_left
  have hJC : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer
      ((source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ).trans
        (normalizer_le_normalizer_centralizer K))).trans inf_normalizer_le_normalizer_inf
  have hn : (C.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hJC
  have hs := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (show Chapter1.IsSylowIn 2 Y J from ⟨P,hP⟩) hCJ hn.isSubnormal
  have hYJ : Y ≤ J := (map_subtype_le _).trans hHJ
  have he : Y ⊓ C = twoCore H := by
    change Y ⊓ (J ⊓ centralizer (K : Set G)) = _
    rw [←inf_assoc, inf_eq_left.mpr hYJ]
    exact (MathieuSourceSetup.core_eq_sylow_centralizer c hgen).symm
  exact he ▸ hs
/-- The literal core centralizer of a noncentral involution in the original
dihedral-core branch is the four generated by that involution and t. -/
theorem source_prime_core_four
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (_hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hmodel : ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)))
    (t i : G) (ht : orderOf t = 2) (hi : orderOf i = 2) (hti : t ≠ i)
    (htC : t ∈ twoCore H) (hiC : i ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype)) :
    twoCore H ⊓ centralizer ({i} : Set G) = zpowers t ⊔ zpowers i ∧
      IsKleinFour (twoCore H ⊓ centralizer ({i} : Set G) : Subgroup G) ∧
      i ∉ centerIn ((S : Subgroup H).map H.subtype) := by
  classical
  let Y := (S : Subgroup H).map H.subtype
  have htCC : t ∈ centralizer (twoCore H : Set G) :=
    centralizer_le (pCoreIn_le_sylow H S) htZ.2
  obtain ⟨he,hfour⟩ := centralizer_core_four (twoCore H)
    (Or.inl hmodel) t i ht hi hti htC hiC htCC
  refine ⟨he,hfour,?_⟩
  intro hiZ
  obtain ⟨hs,hd,hcard,_⟩ := MathieuSourceSetup.normal_component_center_split c hG hempty hgen hb
  have hcc : Nat.card (centerIn Y ⊓ twoCore H : Subgroup G) = 2 :=
    (MathieuSourceSetup.center_four_of_center_split c hgen (centerIn Y ⊓ K) hs hd hcard).2
  have hline : centerIn Y ⊓ twoCore H = zpowers t := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr (show t ∈ centerIn Y ⊓ twoCore H from ⟨htZ,htC⟩)) ?_).symm
    rw [hcc,Nat.card_zpowers,ht]
  have him : i ∈ zpowers t := hline ▸ (show i ∈ centerIn Y ⊓ twoCore H from ⟨hiZ,hiC⟩)
  rw [mem_zpowers_iff_mem_range_orderOf,ht] at him
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp him
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · simp only [pow_zero,orderOf_one] at hi; omega
  · exact hti (pow_one t).symm
/-- The actual four-group is Sylow in the simultaneous centralizer of t,
i, and K. Uniform self-centralization of fours in the core supplies maximality. -/
theorem source_prime_core_four_sylow
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hmodel : ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)))
    (t i : G) (ht : orderOf t = 2) (hi : orderOf i = 2) (hti : t ≠ i)
    (htC : t ∈ twoCore H) (hiC : i ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype)) :
    Chapter1.IsSylowIn 2 (twoCore H ⊓ centralizer ({i} : Set G))
      (centralizer ({t} : Set G) ⊓ centralizer (K : Set G) ⊓ centralizer ({i} : Set G)) := by
  let C := centralizer ({t} : Set G) ⊓ centralizer (K : Set G)
  let R := twoCore H ⊓ centralizer ({i} : Set G)
  obtain ⟨he,hfour,_⟩ := source_prime_core_four c hG hempty hgen hb hstar hmodel
    t i ht hi hti htC hiC htZ
  have hs := source_core_sylow_centralizer c hG hempty hgen hb hstar t ht htC htZ
  have hCC : twoCore H ≤ C := (Chapter1.isSylowIn_iff.mp hs).2.1
  have hRC : R ≤ C := inf_le_left.trans hCC
  obtain ⟨P,hP⟩ := hs
  let Ri := R.subgroupOf C
  let eR := subgroupOfEquivOfLe hRC
  have hRi : IsKleinFour Ri := {
    card_four := (Nat.card_congr eR.toEquiv).trans hfour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eR).trans hfour.exponent_two }
  have hself (V : Subgroup C) (hV : IsKleinFour V) (hVP : V ≤ (P : Subgroup C)) :
      (P : Subgroup C) ⊓ centralizer (V : Set C) ≤ V := by
    let eV := V.equivMapOfInjective C.subtype C.subtype_injective
    have hW : IsKleinFour (V.map C.subtype) := {
      card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two }
    have hWC : V.map C.subtype ≤ twoCore H := (map_mono hVP).trans_eq hP
    have hbnd := ambient_four_selfcentralizing (twoCore H)
      (Or.inl hmodel) (V.map C.subtype) hW hWC
    intro q hq
    have hm : (q : G) ∈ V.map C.subtype := hbnd ⟨hP ▸ mem_map_of_mem C.subtype hq.1, by
      rintro w ⟨v,hv,rfl⟩
      exact congrArg Subtype.val (hq.2 v hv)⟩
    obtain ⟨v,hv,hve⟩ := hm
    exact (Subtype.ext hve : v = q) ▸ hv
  obtain ⟨Q,hQR⟩ := Theory.GroupTheory.FourCentralizerSylow.exists_sylow_centralizer P hself Ri hRi
  have hsRi : Chapter1.IsSylowIn 2 Ri (centralizer (Ri : Set C)) := ⟨Q,hQR⟩
  have hsR := Chapter1.Section02.IndexTwo.isSylowIn_map hsRi C.subtype
  rw [Subgroup.map_centralizer_subtype, map_subgroupOf_eq_of_le hRC] at hsR
  have hcent : C ⊓ centralizer (R : Set G) = C ⊓ centralizer ({i} : Set G) := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      intro a ha
      exact mem_centralizer_singleton_iff.mpr
        (ha.2 i (show i ∈ R from ⟨hiC, mem_centralizer_singleton_iff.mpr rfl⟩)).symm
    · refine le_inf inf_le_left ?_
      intro a ha r hr
      have hRa : R ≤ centralizer ({a} : Set G) := by
        rw [show R = zpowers t ⊔ zpowers i from he]
        apply sup_le
        · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
            (mem_centralizer_singleton_iff.mp ha.1.1).symm)
        · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
            (mem_centralizer_singleton_iff.mp ha.2).symm)
      exact mem_centralizer_singleton_iff.mp (hRa hr)
  exact hcent ▸ hsR
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
