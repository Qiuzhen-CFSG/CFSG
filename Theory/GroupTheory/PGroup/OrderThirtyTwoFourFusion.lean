module
public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition
/-!
# Fusion of a normal four in a Sylow subgroup of order 32

If the three involutions of a normal four are fused, its index-two
centralizer has no characteristic subgroup of order two, provided the
Sylow center has a unique involution and the elementary rank is at most two.

A characteristic subgroup of order two would be the central involution.
Conjugate a different element of the four to that involution, and extend
this conjugation to an embedding of its centralizer into the Sylow subgroup.
The embedded centralizer still has index two, so the characteristic subgroup
again maps to the central involution, contradicting injectivity.

This is a direct small-order substitute for the MacWilliams inputs 1.3–1.4
in Janko–Thompson, Math. Z. 113 (1970), pp.386 and 393. It needs no ambient
simplicity or local-solvability hypothesis. The order-sixteen recognition
then identifies the centralizer as `C₄ × C₄`.
-/

open Subgroup

namespace Sylow

/-- Conjugacy to a central Sylow element extends to an embedding of any
subgroup centralized by the source element. -/
public theorem exists_injective_hom_of_central_isConj
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (C : Subgroup S) (x : C) (hx : x ∈ center C)
    (z : S) (hz : z ∈ center S) (hconj : IsConj ((x : S) : G) (z : G)) :
    ∃ f : C →* S, Function.Injective f ∧ f x = z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let Z := centralizer ({(z : G)} : Set G)
  have hSZ : (S : Subgroup G) ≤ Z := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz (⟨s, hs⟩ : S)))
  let f₀ : C →* G := (MulAut.conj g).toMonoidHom.comp
    ((S : Subgroup G).subtype.comp C.subtype)
  have hf₀ : Function.Injective f₀ := (MulAut.conj g).injective.comp
    ((S : Subgroup G).subtype_injective.comp C.subtype_injective)
  have hf₀x : f₀ x = z := hg
  have hfZ (c : C) : f₀ c ∈ Z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hf₀x, ← map_mul, ← map_mul, mem_center_iff.mp hx c]
  let f : C →* Z := f₀.codRestrict Z hfZ
  obtain ⟨Q, hQ⟩ := ((S.isPGroup'.to_subgroup C).of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq Z Q (S.subtype hSZ)
  have hinS (c : C) : ((n : G) * f₀ c * (n : G)⁻¹) ∈ (S : Subgroup G) := by
    have hm : n * f c * n⁻¹ ∈ (n • Q : Sylow p Z) := by
      exact ⟨f c, hQ ⟨c, rfl⟩, rfl⟩
    rw [hn] at hm
    exact hm
  let F : C →* S := ((MulAut.conj (n : G)).toMonoidHom.comp f₀).codRestrict
    (S : Subgroup G) hinS
  refine ⟨F, ?_, ?_⟩
  · intro a b hab
    exact hf₀ ((MulAut.conj (n : G)).injective (congrArg Subtype.val hab))
  · apply Subtype.ext
    change (n : G) * f₀ x * (n : G)⁻¹ = z
    rw [hf₀x]
    have hc := mem_centralizer_singleton_iff.mp n.property
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]

end Sylow

namespace Subgroup

private theorem normal_map_of_characteristic_of_injective
    {H P : Type*} [Group H] [Group P]
    (f : H →* P) (hf : Function.Injective f) [f.range.Normal]
    (K : Subgroup H) [K.Characteristic] : (K.map f).Normal := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  refine ⟨?_⟩
  rintro _ ⟨k, hk, rfl⟩ g
  let α : MulAut H := (e.trans (MulAut.conjNormal g)).trans e.symm
  refine ⟨α k, characteristic_iff_le_comap.mp inferInstance α hk, ?_⟩
  have h := e.apply_symm_apply ((MulAut.conjNormal g) (e k))
  exact congrArg Subtype.val h

private theorem normal_card_two_eq_omega_center
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (K : Subgroup P) [K.Normal] (hK : Nat.card K = 2) :
    K = (omega₁ (center P) (p := 2)).map (center P).subtype := by
  have hcentral := central_of_normal_card_two K hK
  apply eq_of_le_of_card_ge
  · intro k hk
    refine ⟨⟨k, hcentral hk⟩, subset_closure ?_, rfl⟩
    change (⟨k, hcentral hk⟩ : center P) ^ (2 ^ 1) = 1
    apply Subtype.ext
    have hpow : (⟨k, hk⟩ : K) ^ 2 = 1 := by
      rw [← hK]
      exact pow_card_eq_one'
    simpa using congrArg Subtype.val hpow
  · rw [card_map_of_injective (center P).subtype_injective, hZ, hK]

end Subgroup

namespace Sylow

/-- Fusion of the normal four excludes characteristic subgroups of order two
in its centralizer. -/
public theorem centralizer_four_no_characteristic_two
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G))
    (K : Subgroup (centralizer (E : Set S))) [K.Characteristic] : Nat.card K ≠ 2 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := centralizer (E : Set S)
  have hCi : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ E hE
  let : C.Normal := C.normal_of_index_eq_two hCi
  have hC : Nat.card C = 16 := by
    have hh := C.card_mul_index
    rw [hCi, hS] at hh
    omega
  intro hK
  let K₀ := K.map C.subtype
  let : K₀.Normal := ConjAct.normal_of_characteristic_of_normal
  have hK₀ : Nat.card K₀ = 2 := (card_map_of_injective C.subtype_injective).trans hK
  have hK₀Z := normal_card_two_eq_omega_center hZ K₀ hK₀
  have hK₀E : K₀ ≤ E := by
    rw [hK₀Z]
    exact omega_one_center_le_four_of_elementary_card_lt_eight hrank E hE
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : K)
  let z : S := (a.val : C)
  have hzK : z ∈ K₀ := mem_map_of_mem C.subtype a.property
  have hz1 : z ≠ 1 := fun hh => ha (Subtype.ext (Subtype.ext hh))
  have hz : z ∈ center S := central_of_normal_card_two K₀ hK₀ hzK
  have hnot : ¬ E ≤ K₀ := by
    intro h
    have hh := card_le_of_le h
    omega
  obtain ⟨x, hxE, hxK⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx1 : x ≠ 1 := fun hh => hxK (hh ▸ K₀.one_mem)
  have hxC : x ∈ C := le_centralizer E hxE
  let xC : C := ⟨x, hxC⟩
  have hxcentral : xC ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property x hxE).symm
  have hconj : IsConj ((xC : S) : G) (z : G) :=
    hfusion ⟨x, hxE⟩ ⟨z, hK₀E hzK⟩
      (fun hh => hx1 (congrArg Subtype.val hh))
      (fun hh => hz1 (congrArg Subtype.val hh))
  obtain ⟨f, hf, hfx⟩ := S.exists_injective_hom_of_central_isConj C xC hxcentral z hz hconj
  have hfr : Nat.card f.range = 16 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩).toEquiv]
    exact hC
  let : f.range.Normal := f.range.normal_of_index_eq_two (by
    have hh := f.range.card_mul_index
    rw [hfr, hS] at hh
    omega)
  let : (K.map f).Normal := normal_map_of_characteristic_of_injective f hf K
  have hKf : Nat.card (K.map f) = 2 := (card_map_of_injective hf).trans hK
  have heq : K.map f = K₀ :=
    (normal_card_two_eq_omega_center hZ (K.map f) hKf).trans hK₀Z.symm
  have hzKf : f xC ∈ K.map f := by rw [hfx, heq]; exact hzK
  obtain ⟨k, hk, he⟩ := hzKf
  have hkx : k = xC := hf he
  exact hxK (mem_map_of_mem C.subtype (hkx ▸ hk))

/-- The centralizer of a fused normal four in this order-32 case is `C₄ × C₄`. -/
public theorem centralizer_four_equiv_c4_square
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Nat.card S = 32)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    Nonempty ((centralizer (E : Set S)) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let C := centralizer (E : Set S)
  have hCi : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ E hE
  have hC : Nat.card C = 16 := by
    have hh := C.card_mul_index
    rw [hCi, hS] at hh
    omega
  have hEC : E ≤ C := le_centralizer E
  have hEZ : E.subgroupOf C ≤ center C := by
    intro e he
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property e he).symm
  have hZC : 4 ≤ Nat.card (center C) := by
    have hh := card_le_of_le hEZ
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, hE] at hh
    exact hh
  have hchar (K : Subgroup C) (hK : K.Characteristic) : Nat.card K ≠ 2 := by
    let : K.Characteristic := hK
    exact S.centralizer_four_no_characteristic_two hS hZ
      (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE hfusion K
  let : IsMulCommutative C :=
    NormalSixteenCommutativity.isMulCommutative_of_card_sixteen_of_no_characteristic_two
      hC hZC hchar
  have hnot : ¬ (∀ x : C, x ^ 2 = 1) := by
    intro hh
    have hel : IsElementaryAbelian 2 C :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hh }
    have hb := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G) C hel
    omega
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  have hd : orderOf x ∣ 2 ^ 4 := by simpa [hC] using orderOf_dvd_natCard x
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hdiv : 4 ∣ orderOf x := by
    have hnotdiv : ¬ orderOf x ∣ 2 := fun hh => hx (orderOf_dvd_iff_pow_eq_one.mp hh)
    rw [he] at hnotdiv ⊢
    interval_cases k <;> norm_num at hnotdiv <;> norm_num
  have hfour : ∃ x : C, orderOf x = 4 :=
    ⟨x ^ (orderOf x / 4), orderOf_pow_orderOf_div (orderOf_pos x).ne' hdiv⟩
  exact NormalSixteenC4Square.recognition_of_no_characteristic_two hC hchar hfour

end Sylow
