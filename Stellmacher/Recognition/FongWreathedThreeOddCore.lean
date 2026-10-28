module

public import Stellmacher.Recognition.FongWreathedBorelCentralizers
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.GroupTheory.CentralizerOddCore
public import Theory.GroupTheory.OrderThreeCentralizer
public import Theory.GroupTheory.OrderThreeNormalizer
public import Theory.GroupTheory.SylowSevenOrder189
public import Theory.GroupAction.NineEightInverter

/-!
# The odd core of Fong's order-three centralizer

For an order-three element inverted by `F`, assume that the indicated cyclic
four-group is a Sylow two-subgroup of its centralizer. Burnside transfer then
identifies the odd core as a normal complement. Its order divides 189.
A factor of seven gives a characteristic subgroup of order seven centralized
by `J`, contradicting the involution centralizer order 96. Thus the core is a
three-group. The ambient Sylow three-center forces its order to be at least
nine. If its order is nine, the action of `F` preserving and inverting `⟨R⟩`
has fourth power trivial, again contradicting the centralizer order 96.
Consequently the core has order 27 and complements `⟨F²⟩` in `C_G(R)`.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), p.75.
-/

namespace Stellmacher.Recognition.FongWreathed

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
variable (P : ABG.Wreathed.Presentation S 2)

omit [Finite G] in
public theorem centralizer_three_sylow_card
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Nat.card T = 4 := by
  rw [← Subgroup.card_map_of_injective (Subgroup.centralizer ({R} : Set G)).subtype_injective,
    hT, Nat.card_zpowers, orderOf_F_sq]

public theorem centralizer_three_oddCore_complement
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    (T : Subgroup (Subgroup.centralizer ({R} : Set G))).IsComplement'
      (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) := by
  let C := Subgroup.centralizer ({R} : Set G)
  have hc : IsCyclic T := by
    let hm : IsCyclic ((T : Subgroup C).map C.subtype) := by rw [hT]; infer_instance
    exact isCyclic_of_injective
      ((T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom
      ((T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).injective
  apply T.isComplement'_pPrimeCore_of_isCyclic hc
  exact (by norm_num : 2 ∣ 4).trans ((centralizer_three_sylow_card P R T hT) ▸
    (T : Subgroup C).card_subgroup_dvd_card)

public theorem centralizer_three_eq_sup_oddCore
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Subgroup.centralizer ({R} : Set G) = Subgroup.zpowers (F P ^ 2) ⊔
      (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))).map
        (Subgroup.centralizer ({R} : Set G)).subtype := by
  have hh := congrArg (Subgroup.map (Subgroup.centralizer ({R} : Set G)).subtype)
    (centralizer_three_oddCore_complement P R T hT).sup_eq_top
  have htop : (⊤ : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.centralizer ({R} : Set G) := by
    ext g
    constructor
    · rintro ⟨a, _, rfl⟩
      exact a.property
    · intro hg
      exact ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩
  simpa only [Subgroup.map_sup, hT, htop] using hh.symm

public theorem card_centralizer_three_eq_four_mul_oddCore
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Nat.card (Subgroup.centralizer ({R} : Set G)) =
      4 * Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) := by
  simpa only [centralizer_three_sylow_card P R T hT] using
    (centralizer_three_oddCore_complement P R T hT).card_mul_card.symm

public theorem oddCore_centralizer_three_card_dvd_189
    (hG : Nat.card G = 6048)
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) ∣ 189 := by
  have hd := (Subgroup.centralizer ({R} : Set G)).card_subgroup_dvd_card
  rw [card_centralizer_three_eq_four_mul_oddCore P R T hT, hG] at hd
  have hd' : Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) ∣ 1512 :=
    (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hd
  exact ((pPrimeCore_coprime_card (p := 2)
    (G := Subgroup.centralizer ({R} : Set G))).symm.pow_right 3).dvd_of_dvd_mul_left hd'

private theorem small_core_le_centralizer_J (R : G) (hR : orderOf R = 3) (hFR : (F P)⁻¹ * R * F P = R⁻¹)
    (hsmall : Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) ≤ 9) :
    (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype ≤
        Subgroup.centralizer ({J P} : Set G) := by
  let C := Subgroup.centralizer ({R} : Set G)
  let O := pPrimeCore 2 C
  let Q := O.map C.subtype
  have hRmem : R ∈ Q := Subgroup.mem_pPrimeCore_centralizer 2 R (by rw [hR]; decide)
  have hFn : F P ∈ Subgroup.normalizer (Subgroup.zpowers R : Set G) := by
    rw [Subgroup.normalizer_zpowers_order_three R (F P) hR hFR]
    exact (show Subgroup.zpowers (F P) ≤ Subgroup.zpowers (F P) ⊔
      Subgroup.centralizer ({R} : Set G) from le_sup_left) (Subgroup.mem_zpowers _)
  have hFQ : F P ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.normalizer_le_normalizer_pPrimeCore_centralizer 2 R hFn
  let v : Subgroup.normalizer (Q : Set G) := ⟨(F P)⁻¹, (Subgroup.normalizer _).inv_mem hFQ⟩
  let f : MulAut Q := Q.normalizerMonoidHom v
  have hf8 : f ^ 8 = 1 := by
    rw [← map_pow]
    have hv : v ^ 8 = 1 := by
      apply Subtype.ext
      change ((F P)⁻¹) ^ 8 = 1
      rw [inv_pow, show F P ^ 8 = 1 by simpa only [orderOf_F] using pow_orderOf_eq_one (F P), inv_one]
    rw [hv, map_one]
  let r : Q := ⟨R, hRmem⟩
  have hr : orderOf r = 3 := by rw [← Subgroup.orderOf_coe r]; exact hR
  have hfr : f r = r⁻¹ := by
    apply Subtype.ext
    change (F P)⁻¹ * R * ((F P)⁻¹)⁻¹ = R⁻¹
    simpa only [inv_inv] using hFR
  have hQ : Nat.card Q ≤ 9 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hsmall
  have hf4 := MulAut.fourth_pow_eq_one_of_card_le_nine_of_inverts_three hQ f hf8 r hr hfr
  intro a ha
  have hh := congrArg (fun e : MulAut Q => (e ⟨a, ha⟩ : G)) hf4
  rw [show f = Q.normalizerMonoidHom v from rfl, ← map_pow] at hh
  change ((F P)⁻¹) ^ 4 * a * (((F P)⁻¹) ^ 4)⁻¹ = a at hh
  have hJinv : (J P)⁻¹ = J P := inv_eq_of_mul_eq_one_right (by
    rw [← pow_two, ← orderOf_J P]; exact pow_orderOf_eq_one _)
  rw [inv_pow, show F P ^ 4 = J P from rfl, hJinv] at hh
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hh).symm

section Simple

variable [IsSimpleGroup G]
variable (hS : ABG.IsWreathedOfHeight S 2) (x : G) (hx : orderOf x = 2)
variable [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]

include hS x hx

public theorem seven_not_dvd_oddCore_centralizer_three
    (hG : Nat.card G = 6048) (c : CharacterData P)
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    ¬ 7 ∣ Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) := by
  intro h7
  let C := Subgroup.centralizer ({R} : Set G)
  let O := pPrimeCore 2 C
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let V : Sylow 7 O := default
  have hd : Nat.card O ∣ 189 := oddCore_centralizer_three_card_dvd_189 P hG R T hT
  have hV : Nat.card V = 7 := V.card_eq_seven_of_card_dvd_189 hd h7
  let : (V : Subgroup O).Characteristic := V.characteristic_of_card_dvd_189 hd h7
  let N : Subgroup C := (V : Subgroup O).map O.subtype
  have hN : Nat.card N = 7 := by rw [Subgroup.card_map_of_injective O.subtype_injective]; exact hV
  let : N.Normal := inferInstanceAs (((V : Subgroup O).map O.subtype).Normal)
  have hu : F P ^ 2 ∈ C := by
    have hm := (Subgroup.mem_zpowers (F P ^ 2))
    rw [← hT] at hm
    exact Subgroup.map_subtype_le _ hm
  let u : C := ⟨F P ^ 2, hu⟩
  have hu4 : u ^ 4 = 1 := by
    apply Subtype.ext
    change (F P ^ 2) ^ 4 = 1
    rw [← pow_mul]
    simpa only [orderOf_F] using pow_orderOf_eq_one (F P)
  have hJ := Subgroup.sq_mem_centralizer_of_normal_card_seven N hN u hu4
  have hle : N.map C.subtype ≤ Subgroup.centralizer ({J P} : Set G) := by
    rintro g ⟨n, hn, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := Subgroup.mem_centralizer_iff.mp hJ n hn
    have hhG := congrArg Subtype.val hh
    change (n : G) * (F P ^ 2) ^ 2 = (F P ^ 2) ^ 2 * (n : G) at hhG
    simpa [← pow_mul, J] using hhG
  have hdiv := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective C.subtype_injective, hN,
    card_centralizer_J P hS x hx hG c] at hdiv
  norm_num at hdiv


/-- The factor of seven is absent, so the odd complement is a three-group. -/
public theorem oddCore_centralizer_three_card_dvd_27
    (hG : Nat.card G = 6048) (c : CharacterData P)
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) ∣ 27 := by
  exact ((show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr
    (seven_not_dvd_oddCore_centralizer_three P hS x hx hG c R T hT)).symm.dvd_of_dvd_mul_left
    (oddCore_centralizer_three_card_dvd_189 P hG R T hT)

public theorem oddCore_centralizer_three_isPGroup
    (hG : Nat.card G = 6048) (c : CharacterData P)
    (R : G) (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    IsPGroup 3 (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) :=
  IsPGroup.of_card_dvd_pow (n := 3)
    (oddCore_centralizer_three_card_dvd_27 P hS x hx hG c R T hT)

/-- Fong’s odd complement has order 27. The ambient Sylow three-center
excludes orders one and three, and the inversion action excludes order nine. -/
public theorem oddCore_centralizer_three_card (hG : Nat.card G = 6048) (c : CharacterData P)
    (R : G) (hR : orderOf R = 3) (hFR : (F P)⁻¹ * R * F P = R⁻¹)
    (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) = 27 := by
  let C := Subgroup.centralizer ({R} : Set G)
  let O := pPrimeCore 2 C
  have hd : Nat.card O ∣ 27 :=
    oddCore_centralizer_three_card_dvd_27 P hS x hx hG c R T hT
  have h9 : 9 ∣ Nat.card O := by
    have hh := Subgroup.nine_dvd_card_centralizer_of_order_three
      (by rw [hG]; norm_num) R hR
    rw [card_centralizer_three_eq_four_mul_oddCore P R T hT] at hh
    exact (show Nat.Coprime 9 4 by decide).dvd_of_dvd_mul_left hh
  have hne : Nat.card O ≠ 9 := by
    intro hO
    have hle := small_core_le_centralizer_J P R hR hFR (by change Nat.card O ≤ 9; omega)
    have hh := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      card_centralizer_J P hS x hx hG c] at hh
    change Nat.card O ∣ 96 at hh
    rw [hO] at hh
    norm_num at hh
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · rw [h] at h9; norm_num at h9
  · rw [h] at h9; norm_num at h9
  · exact (hne h).elim
  · exact h


/-- The two conditional conclusions needed for the Borel subgroup construction. -/
public theorem centralizer_three_oddCore_data
    (hG : Nat.card G = 6048) (c : CharacterData P)
    (R : G) (hR : orderOf R = 3) (hFR : (F P)⁻¹ * R * F P = R⁻¹)
    (T : Sylow 2 (Subgroup.centralizer ({R} : Set G)))
    (hT : (T : Subgroup (Subgroup.centralizer ({R} : Set G))).map
      (Subgroup.centralizer ({R} : Set G)).subtype = Subgroup.zpowers (F P ^ 2)) :
    Nat.card (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))) = 27 ∧
      Subgroup.centralizer ({R} : Set G) = Subgroup.zpowers (F P ^ 2) ⊔
        (pPrimeCore 2 (Subgroup.centralizer ({R} : Set G))).map
          (Subgroup.centralizer ({R} : Set G)).subtype :=
  ⟨oddCore_centralizer_three_card P hS x hx hG c R hR hFR T hT,
    centralizer_three_eq_sup_oddCore P R T hT⟩

end Simple
end Stellmacher.Recognition.FongWreathed
