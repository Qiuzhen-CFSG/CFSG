module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstProjective
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import Theory.GroupAction.PrimeFixedQuotient
public import Theory.GroupTheory.PrimeOrderConjugation
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.SpecialLinear
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem cubic_not_in_two_group {N : Subgroup G} (hN : IsPGroup 2 N)
    {y : G} (hy : orderOf y = 3) : y ∉ N := by
  intro hm
  have hc := hN.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨y,hm⟩ : N)
  rw [orderOf_mk,hy] at hc
  norm_num at hc

omit [Finite G] in
private theorem cubic_quotient_order (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    {y : G} (hy : orderOf y = 3) : orderOf (QuotientGroup.mk' N y) = 3 := by
  apply orderOf_eq_prime
  · rw [←map_pow,←hy,pow_orderOf_eq_one,map_one]
  · exact fun he => cubic_not_in_two_group hN hy ((QuotientGroup.eq_one_iff _).mp he)

private theorem fixed_cubic (A E : Subgroup G) (hE : IsPGroup 3 E)
    (hEA : E ≤ Closure.coreQuotientCentralizer A)
    (hcard : 3 ∣ Nat.card (A ⧸ pCore 2 A)) :
    ∃ y : G, y ∈ A ∧ y ∈ centralizer (E : Set G) ∧ orderOf y = 3 := by
  have hcop : ¬ 3 ∣ Nat.card (pCore 2 A) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hEN : E ≤ normalizer (A : Set G) :=
    hEA.trans (map_subtype_le _)
  let t := (QuotientGroup.mk' (pCore 2 A)).comp
    (inclusion (show A ⊓ centralizer (E : Set G) ≤ A from inf_le_left))
  have ht : Function.Surjective t := centralizer_quotient_surjective_of_prime_fixed
    A E (pCore 2 A) hE hEN hcop (fun e he a ha =>
      Closure.coreQuotientCentralizer_commutator (hEA he) ha)
  let C := A ⊓ centralizer (E : Set G)
  have hdiv : 3 ∣ Nat.card C := hcard.trans (Subgroup.card_dvd_of_surjective t ht)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hdiv
  let yG : G := y
  exact ⟨yG,y.property.1,y.property.2,(orderOf_coe y).trans hy⟩

/-- Restriction of the ambient two-core suffices to detect noncentral cubics. -/
private theorem cubic_image_not_central (A B : Subgroup G) (hAB : A ≤ B)
    (hzA : center (A ⧸ pCore 2 A) = ⊥)
    {y : G} (hyA : y ∈ A) (hy : orderOf y = 3) :
    QuotientGroup.mk' (pCore 2 G) y ∉
      (center (B.map (QuotientGroup.mk' (pCore 2 G)))).map
        (B.map (QuotientGroup.mk' (pCore 2 G))).subtype := by
  have _hfinite := Nat.card_pos (α := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let a := QuotientGroup.mk' (pCore 2 A)
  have hres : (pCore 2 G).comap A.subtype ≤ pCore 2 A :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective A.subtype Subtype.val_injective⟩
  rintro ⟨z,hz,hzy⟩
  change (z : G ⧸ pCore 2 G) = q y at hzy
  have hcentral : a ⟨y,hyA⟩ ∈ center (A ⧸ pCore 2 A) := by
    apply mem_center_iff.mpr
    intro b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) b
    have he : q (b : G) * q y = q y * q (b : G) := by
      have hh := congrArg Subtype.val (mem_center_iff.mp hz
        (⟨q b,mem_map_of_mem q (hAB b.property)⟩ : B.map q))
      simpa only [Subgroup.coe_mul,hzy] using hh
    have hc : ⁅b,(⟨y,hyA⟩ : A)⁆ ∈ pCore 2 A := by
      apply hres
      apply (QuotientGroup.eq_one_iff (N := pCore 2 G) _).mp
      change q ((b : G) * y * (b : G)⁻¹ * y⁻¹) = 1
      simp only [map_mul,map_inv]
      rw [he]
      group
    have hc' := (QuotientGroup.eq_one_iff (N := pCore 2 A) _).mpr hc
    change a ⁅b,(⟨y,hyA⟩ : A)⁆ = 1 at hc'
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hc'
    exact hc'
  have hycore := (QuotientGroup.eq_one_iff (N := pCore 2 A) _).mp (hzA.le hcentral)
  exact cubic_not_in_two_group (pCore_isPGroup (p := 2) (G := A))
    (by simpa only [orderOf_mk] using hy) hycore

private theorem rank_three_of_central_cubic (B : Subgroup G) [B.Normal]
    (hZ : Nat.card (center B) = 3) (x y : G)
    (hx : orderOf x = 3) (hy : orderOf y = 3) (hxB : x ∉ B) (hyB : y ∈ B)
    (hxy : x * y = y * x)
    (hyZ : y ∉ (center B).map B.subtype) : 3 ≤ primeRank 3 G := by
  let Z := (center B).map B.subtype
  have hZc : Nat.card Z = 3 := (Nat.card_congr
    (equivMapOfInjective (center B) B.subtype Subtype.val_injective).toEquiv).symm.trans hZ
  let : IsElementaryAbelian 3 (center B) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun z => by simpa only [hZ] using pow_card_eq_one' (x := z)) }
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.map B.subtype
  have hZN : (⊤ : Subgroup G) ≤ normalizer (Z : Set G) := by
    apply le_normalizer_iff.mpr
    rintro g _ _ ⟨z,hz,rfl⟩
    exact ⟨MulAut.conjNormal g z, ((centerCongr (MulAut.conjNormal g)) ⟨z,hz⟩).property,rfl⟩
  have hxZ : x ∈ centralizer (Z : Set G) :=
    le_centralizer_of_prime_card_of_le_normalizer Z (zpowers x) Nat.prime_three hZc
      ((Nat.card_zpowers x).trans hx) (le_top.trans hZN) (mem_zpowers x)
  have hyfix : Z ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨z,hz,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (mem_center_iff.mp hz (⟨y,hyB⟩ : B))).symm
  obtain ⟨he,hcard⟩ := IsElementaryAbelian.fixed_join_card (n := 1) Z y hy
    (disjoint_zpowers_of_prime_order_not_mem Z y hy hyZ) hyfix (by simpa using hZc)
  let := he
  have hEB : Z ⊔ zpowers y ≤ B := sup_le (map_subtype_le _) (zpowers_le.mpr hyB)
  have hfix : Z ⊔ zpowers y ≤ centralizer ({x} : Set G) := by
    refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxy.symm))
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxZ z hz)
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join (Z ⊔ zpowers y) x hx
    (fun hm => hxB (hEB hm)) hfix hcard
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.SpecialLinear

open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open SpecialLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual quotient-centralizing faithful Cartan cubic excludes the SL₃(4)
cover: its image and a noncentral fixed cubic force three-rank at least three. -/
theorem first_component_not_specialLinearFour
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥) :
    ¬ Source.IsSL (K ⧸ pCore 2 K) 3 4 := by
  rintro ⟨F,_,_,hF,⟨eK⟩⟩
  let H := normalizer (f.Vi 0 : Set G)
  let B := K.subgroupOf H
  let A := (f.Li 0).subgroupOf H
  let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
  have hAH : f.Li 0 ≤ H := hLK.trans hK.1.1
  have hEH : E ≤ H := inf_le_left.trans (f.cartan_normalizes hu hX 0)
  have hEc : Nat.card E = 3 := by simpa [E,hfour] using hXcard
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 1) (by simpa using hEc)
  have heA : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F₀,_,_,hF₀,⟨e⟩⟩ := hm
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card F₀ = 4 by simpa [hfour] using hF₀)
    exact ⟨e.trans a⟩
  obtain ⟨eA⟩ := heA
  have hAc : Nat.card (f.Li 0 ⧸ pCore 2 (f.Li 0)) = 60 := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num
  obtain ⟨y,hyA,hyE,hy⟩ := fixed_cubic (f.Li 0) E hEp inf_le_right (by rw [hAc]; decide)
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 (by rw [hEc])
  have hxG : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
  have hxK : (x : G) ∉ K := by
    intro hxK
    have he : (x : G) = 1 :=
      (first_component_disjoint_of_faithful_cartan D S f hm hfix hK.1 hLK hfaith).le_bot
        ⟨hxK,x.property⟩
    rw [he,orderOf_one] at hxG
    contradiction
  let xH : H := ⟨x,hEH x.property⟩
  let yH : H := ⟨y,hAH hyA⟩
  have hxH : orderOf xH = 3 := (orderOf_coe xH).symm.trans hxG
  have hyH : orderOf yH = 3 := (orderOf_coe yH).symm.trans hy
  let : B.Normal := hK.2
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := B.map q
  let : C.Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
  let b : (B ⧸ pCore 2 B) ≃* (K ⧸ pCore 2 K) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1.1) (pCore_map_iso 2 _)
  let eC : C ≃* SL(3,F) := (cComponentTwoCoreQuotientEquiv hK.1.2).symm.trans (b.trans eK)
  have hZ : Nat.card (center C) = 3 := by
    rw [Nat.card_congr (centerCongr eC).toEquiv,Atlas.ExceptionalSupport.card_sl_center,hF]
    decide
  let a : (A ⧸ pCore 2 A) ≃* (f.Li 0 ⧸ pCore 2 (f.Li 0)) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hAH) (pCore_map_iso 2 _)
  have hzA : center (A ⧸ pCore 2 A) = ⊥ := by
    apply bot_unique
    intro z hz
    apply (a.trans eA).map_eq_one_iff.mp
    exact (alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 5))).le
      ((centerCongr (a.trans eA)) ⟨z,hz⟩).property
  have hout : q xH ∉ C := fun hi => hxK
    (CComponentPrimeRank.prime_actor_mem_of_twoGroup_image (pCore 2 H) B pCore_isPGroup
      (by decide : Odd 3) xH hxH hi)
  have hxy : q xH * q yH = q yH * q xH := by
    rw [←map_mul,←map_mul]
    exact congrArg q (Subtype.ext ((mem_centralizer_iff.mp hyE) x x.property))
  have hlarge := rank_three_of_central_cubic C hZ (q xH) (q yH)
    (cubic_quotient_order _ pCore_isPGroup hxH) (cubic_quotient_order _ pCore_isPGroup hyH)
    hout (mem_map_of_mem q (hLK hyA)) hxy
    (cubic_image_not_central A B (comap_mono hLK) hzA hyA hyH)
  have hr : primeRank 3 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
        3 Nat.prime_three (by decide))
  omega

/-- The first-normalizer sieve, with all covering rows discharged, retains
only the genuine refinements and the literal PGL₃(4) quotient. -/
theorem first_reduction_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementReduction L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  rcases first_reduction_or_specialLinearFour_of_cartan D S f hu hm hfix hNT hX hK hLK
    hXcard hfaith hk with h | ⟨hn,hs⟩
  · exact h
  · exact (first_component_not_specialLinearFour D S f hu hm hn hfix hX hK hLK
      hXcard hfaith hs).elim
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
