module
public import Stellmacher.Recognition.FongWreathedCoordinates
public import ABG.ChapterII.Section1.WreathedOrderEightCentralizer
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.CyclicSylowCenterNormalizer
public import Theory.GroupTheory.CyclicEightNormalizer
public import Theory.GroupTheory.PPrimeCoreSubgroup

/-!
# The actual normalizer in Fong's height-two presentation

For any finite group with a height-two wreathed Sylow subgroup, the actual
normalizer of ⟨F⟩ is C(F)⟨X⟩. Its odd core centralizes F and its quotient
has order sixteen. These statements do not need simplicity, a fusion
orientation, or solvability of an involution centralizer.

The cyclic subgroup ⟨F²⟩ lies in the Sylow center, so its normalizer
centralizes it. Thus F² is not conjugate to its inverse. Every Sylow
subgroup of C(F) is ⟨F⟩: embed it into an ambient Sylow subgroup and use
the order-eight centralizer calculation. Burnside transfer supplies its
odd complement. The cyclic-eight normalizer theorem then gives the result.

Source: P. Fong, Some Sylow subgroups of order 32 and a characterization
of U(3,3), J. Algebra 6 (1967), printed p. 72, first paragraph.
-/

namespace Stellmacher.Recognition.FongWreathedIntrinsic
open ABG
variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

private theorem square_not_real :
    ¬ IsConj ((F P ^ 2 : S) : G) (((F P ^ 2)⁻¹ : S) : G) := by
  let a : G := ((F P ^ 2 : S) : G)
  let C := Subgroup.zpowers a
  have hCS : C ≤ (S : Subgroup G) :=
    Subgroup.zpowers_le.mpr (F P ^ 2).property
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer (C : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    intro s hs
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (F_sq_mem_center P) (⟨s, hs⟩ : S))
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hgN : g ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * a * g⁻¹) = Subgroup.zpowers a
    rw [show g * a * g⁻¹ = a⁻¹ from hg, Subgroup.zpowers_inv]
  have hgC := Subgroup.normalizer_le_centralizer_of_cyclic_sylow_center S C hCS hSC hgN
  have hc : g * a = a * g :=
    ((Subgroup.mem_centralizer_iff.mp hgC) a (Subgroup.mem_zpowers a)).symm
  have hai : a = a⁻¹ := ((mul_inv_eq_iff_eq_mul).mpr hc).symm.trans hg
  have ha2 : a ^ 2 = 1 := by
    calc
      a ^ 2 = a * a⁻¹ := by rw [pow_two]; exact congrArg (a * ·) hai
      _ = 1 := mul_inv_cancel a
  have hd := orderOf_dvd_of_pow_eq_one ha2
  have ho : orderOf a = 4 := (Subgroup.orderOf_coe _).trans (F_sq_orderOf P)
  rw [ho] at hd
  norm_num at hd

include S P in
private theorem centralizer_cyclic_sylow (y : G) (hy : orderOf y = 8)
    (R : Sylow 2 (Subgroup.centralizer ({y} : Set G))) :
    (R : Subgroup (Subgroup.centralizer ({y} : Set G))) =
      Subgroup.zpowers ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
  let C := Subgroup.centralizer ({y} : Set G)
  let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hycent : yC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property)
  have hZle : Subgroup.zpowers yC ≤ Subgroup.center C := Subgroup.zpowers_le.mpr hycent
  let : (Subgroup.zpowers yC).Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZle hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hZtwo : IsPGroup 2 (Subgroup.zpowers yC) := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe yC, hy]
    rfl
  have hZR := hZtwo.le_sylow_of_normal R
  have hyR : yC ∈ (R : Subgroup C) := hZR (Subgroup.mem_zpowers yC)
  obtain ⟨Q, hQ⟩ := R.exists_comap_subtype_eq
  let yQ : Q := ⟨y, show yC ∈ (Q : Subgroup G).comap C.subtype from hQ.symm ▸ hyR⟩
  let e : Q ≃* S := Sylow.equiv Q S
  apply le_antisymm
  · intro c hc
    let cQ : Q := ⟨c.val, show c ∈ (Q : Subgroup G).comap C.subtype from hQ.symm ▸ hc⟩
    have hec : e cQ ∈ Subgroup.centralizer ({e yQ} : Set S) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.property))
    rw [P.centralizer_eq_zpowers_of_order_eight (e yQ)
      ((e.orderOf_eq yQ).trans ((Subgroup.orderOf_coe yQ).symm.trans hy))] at hec
    obtain ⟨n, hn⟩ := hec
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have heq : yQ ^ n = cQ := e.injective (by simpa only [map_zpow] using hn)
    exact congrArg (fun t : Q => (t : G)) heq
  · exact hZR

private theorem centralizer_odd_quotient_eight :
    Nat.card ((Subgroup.centralizer ({((F P : S) : G)} : Set G)) ⧸
      pPrimeCore 2 (Subgroup.centralizer ({((F P : S) : G)} : Set G))) = 8 := by
  let C := Subgroup.centralizer ({((F P : S) : G)} : Set G)
  let R : Sylow 2 C := Classical.arbitrary _
  have heq := centralizer_cyclic_sylow S P ((F P : S) : G)
    ((Subgroup.orderOf_coe _).trans (F_orderOf P)) R
  have hcard : Nat.card R = 8 := by
    rw [heq, Nat.card_zpowers]
    exact (Subgroup.orderOf_coe (⟨((F P : S) : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : C)).symm.trans
      ((Subgroup.orderOf_coe (F P)).trans (F_orderOf P))
  have hcyc : IsCyclic R := by
    rw [heq]
    infer_instance
  have heven : 2 ∣ Nat.card C := (by omega : 2 ∣ Nat.card R).trans
    (R : Subgroup C).card_subgroup_dvd_card
  exact (R.isComplement'_pPrimeCore_of_isCyclic hcyc heven).index_eq_card.trans hcard

omit [Finite G] in
private theorem x_square : ((X P : S) : G) ^ 2 = 1 := by
  simpa only [← Subgroup.coe_pow, X_orderOf, Subgroup.coe_one] using
    congrArg (fun s : S => (s : G)) (pow_orderOf_eq_one (X P))

omit [Finite G] in
private theorem x_conjugates :
    ((X P : S) : G) * ((F P : S) : G) * ((X P : S) : G)⁻¹ =
      ((F P : S) : G) ^ 5 := by
  have hi : ((X P : S) : G)⁻¹ = ((X P : S) : G) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using x_square S P
  rw [hi]
  exact congrArg Subtype.val (X_conj_F P)

public theorem actualNormalizer_structure :
    let H := Subgroup.normalizer (Subgroup.zpowers ((F P : S) : G) : Set G)
    H = Subgroup.centralizer ({((F P : S) : G)} : Set G) ⊔
      Subgroup.zpowers ((X P : S) : G) ∧
    Nat.card (H ⧸ pPrimeCore 2 H) = 16 ∧
      pPrimeCore 2 H ≤ (Subgroup.centralizer ({((F P : S) : G)} : Set G)).subgroupOf H := by
  have ho : orderOf ((F P : S) : G) = 8 := (Subgroup.orderOf_coe _).trans (F_orderOf P)
  have hn : ¬ IsConj (((F P : S) : G) ^ 2) ((((F P : S) : G) ^ 2)⁻¹) :=
    square_not_real S P
  exact ⟨Subgroup.normalizer_zpowers_eq_centralizer_sup _ _ ho (x_square S P)
      (x_conjugates S P) hn,
    Subgroup.normalizer_oddCore_contract _ _ ho (x_conjugates S P) hn
      (centralizer_odd_quotient_eight S P)⟩
@[expose] public def actualNormalizer : Subgroup G :=
  Subgroup.normalizer (Subgroup.zpowers ((F P : S) : G) : Set G)

@[expose] public def normalizerF : actualNormalizer S P :=
  ⟨((F P : S) : G), (Subgroup.zpowers _).le_normalizer (Subgroup.mem_zpowers _)⟩

@[expose] public def normalizerX : actualNormalizer S P :=
  ⟨((X P : S) : G), by
    change ((X P : S) : G) ∈ Subgroup.normalizer (Subgroup.zpowers ((F P : S) : G) : Set G)
    rw [(actualNormalizer_structure S P).1]
    exact (show Subgroup.zpowers ((X P : S) : G) ≤ _ from le_sup_right)
      (Subgroup.mem_zpowers _)⟩

omit [Finite G] in
public theorem normalizerF_order : orderOf (normalizerF S P) = 8 := by
  exact (Subgroup.orderOf_coe (normalizerF S P)).symm.trans
    ((Subgroup.orderOf_coe (F P)).trans (F_orderOf P))

public theorem normalizerX_sq : normalizerX S P ^ 2 = 1 := by
  apply Subtype.ext
  change ((X P : S) : G) ^ 2 = 1
  have hs : X P ^ 2 = 1 := by simpa only [X_orderOf] using pow_orderOf_eq_one (X P)
  exact congrArg Subtype.val hs

public theorem normalizerX_conjugate :
    normalizerX S P * normalizerF S P * (normalizerX S P)⁻¹ = normalizerF S P ^ 5 := by
  have hi : (normalizerX S P)⁻¹ = normalizerX S P := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using normalizerX_sq S P
  rw [hi]
  apply Subtype.ext
  exact congrArg (fun s : S => (s : G)) (X_conj_F P)

public theorem normalizer_oddCore_odd : Odd (Nat.card (pPrimeCore 2 (actualNormalizer S P))) :=
  (pPrimeCore_coprime_card (p := 2)).odd_of_left

public theorem normalizerF_commute_oddCore (u : pPrimeCore 2 (actualNormalizer S P)) :
    Commute (normalizerF S P) (u : actualNormalizer S P) := by
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    ((actualNormalizer_structure S P).2.2 u.property)).symm

public theorem normalizer_quotient_card :
    Nat.card (actualNormalizer S P ⧸ pPrimeCore 2 (actualNormalizer S P)) = 16 :=
  (actualNormalizer_structure S P).2.1

public theorem normalizer_quotientF_order :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 (actualNormalizer S P)) (normalizerF S P)) = 8 := by
  let K := Subgroup.zpowers (normalizerF S P)
  have hK : IsPGroup 2 K := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_zpowers, normalizerF_order]
    rfl
  have hi := IsPGroup.quotient_pPrimeCore_injective K hK
  have ho := orderOf_injective
    ((QuotientGroup.mk' (pPrimeCore 2 (actualNormalizer S P))).comp K.subtype)
    hi (⟨normalizerF S P, Subgroup.mem_zpowers _⟩ : K)
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply,
    Subgroup.orderOf_mk, normalizerF_order] using ho

end Stellmacher.Recognition.FongWreathedIntrinsic

