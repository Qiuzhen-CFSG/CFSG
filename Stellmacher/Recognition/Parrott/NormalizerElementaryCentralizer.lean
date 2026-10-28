module

public import Stellmacher.Recognition.Parrott.NormalizerCoreThreeCenters

/-!
# The order-256 centralizer in the second normalizer

Put H=C_G(z), J=O₂(H), E=J′, N=N_G(F), K=O₂(N), and U=Ω₁(K),
with all subgroups embedded in G. For w in (E∩F)−Z(U), we prove
C_N(w)=C_J(w), and hence |C_N(w)|=256.

First, an outer involution in the supplied Sylow subgroup acts on
E/⟨z⟩ with four fixed points. Their inverse image has order eight and
is precisely Z(U). The cyclic Sylow image in H/J implies that every
element of T−J fixes only elements of E lying in Z(U).

Next Z(U) and w generate E∩F. Thus C_N(w) normalizes E∩F, its
centralizer E∨F, and the characteristic derived line ⟨z⟩. Consequently
C_N(w) lies in C_N(z)=T. The first step places it in J, and the original
core commutator-pairing count supplies the order 256. This argument
requires neither the subsequent 24-point orbit nor a fusion assertion.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the centralizer calculation immediately after C_K(Q)=⟨b⟩.
The local quotient calculation follows the existing proofs in
`OuterCoreFixedCentralization` and `NormalizerCoreOmegaCentralization`.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

private theorem quotient_fixed_card
    {G : Type*} [Group G] [Finite G] (z : G)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let Z := (center J).subgroupOf D
    ∀ f : (H ⧸ J) →* MulAut (D ⧸ Z), Function.Injective f →
      ∀ y : H, orderOf y = 2 → y ∉ J →
        Nat.card ((FixedPoints.subgroup (zpowers (f (QuotientGroup.mk' J y)))
          (D ⧸ Z)).comap (QuotientGroup.mk' Z)) = 8 := by
  classical
  intro H J D Z f hf y hy hyJ
  let W := D ⧸ Z
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' Z
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hy2J : y ^ 2 ∈ J := (hy ▸ pow_orderOf_eq_one y) ▸ J.one_mem
  obtain ⟨hZmap, _, _, _, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  change IsElementaryAbelian 2 D at hElem
  let : IsElementaryAbelian 2 D := hElem
  change Nat.card D = 32 at hDcard
  change D = Subgroup.upperCentralSeries J 2 at hUpper
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide)
  have hZJcard : Nat.card (center J) = 2 := by
    have hh := card_map_of_injective (K := center J)
      (f := H.subtype.comp J.subtype) (H.subtype_injective.comp J.subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hh
    exact hh.symm
  have hZcard : Nat.card Z = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZJcard
  have hWcard : Nat.card W = 16 := by
    have hh := Z.index_mul_card
    change Nat.card W * Nat.card Z = Nat.card D at hh
    rw [hZcard, hDcard] at hh
    omega
  let : IsElementaryAbelian 2 W := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Group.exponent_quotient_dvd Z).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let g : M →* MulAut W := f.comp e.symm.toMonoidHom
  have hg : Function.Injective g := hf.comp e.symm.injective
  let u : Multiplicative (ZMod 5) := Multiplicative.ofAdd 1
  have hu : orderOf u = 5 := by
    change orderOf (Multiplicative.ofAdd (1 : ZMod 5)) = 5
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  let a : MulAut W := g (SemidirectProduct.inl u)
  let b : MulAut W := f (qJ y)
  have ha : orderOf a = 5 := by
    rw [orderOf_injective g hg, orderOf_injective SemidirectProduct.inl
      SemidirectProduct.inl_injective]
    exact hu
  have hybarSquare : qJ (y ^ 2) = 1 := (QuotientGroup.eq_one_iff _).mpr hy2J
  have hb2 : b ^ 2 = 1 := by
    dsimp [b]
    rw [← map_pow, ← map_pow, hybarSquare, map_one]
  have hybar2 : orderOf (e (qJ y)) = 2 := by
    rw [e.orderOf_eq]
    apply orderOf_eq_prime
    · rw [← map_pow, hybarSquare]
    · intro heq
      exact hyJ ((QuotientGroup.eq_one_iff y).mp heq)
  have hab : b * a * b⁻¹ = a⁻¹ := by
    have hh := congrArg g (faithful_five_four_involution_inverts_left φ hφ
      (e (qJ y)) hybar2 u)
    have hgy : g (e (qJ y)) = b := by simp only [g, b, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    have hgyinv : g ((e (qJ y))⁻¹) = b⁻¹ :=
      (map_inv g _).trans (congrArg Inv.inv hgy)
    have hright : g (SemidirectProduct.inl u⁻¹) = a⁻¹ :=
      (g.comp SemidirectProduct.inl).map_inv u
    rw [map_mul, map_mul, hgy, hgyinv, hright] at hh
    exact hh
  have hfixedW : Nat.card (FixedPoints.subgroup (zpowers b) W) = 4 :=
    card_fixed_of_involution_inverting_five_on_sixteen hWcard a b ha hb2 hab
  let C := FixedPoints.subgroup (zpowers b) W
  have hidx : C.index = 4 := by
    have hc := C.card_mul_index
    rw [hfixedW, hWcard] at hc
    omega
  change Nat.card (C.comap qD) = 8
  have hc := (C.comap qD).card_mul_index
  rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z), hidx, hDcard] at hc
  omega

namespace ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem quotient_involution_eq_or_square (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    ∀ x y : H, (x : G) ∈ (d.sylow : Subgroup G) →
      (y : G) ∈ (d.sylow : Subgroup G) → x ∉ J → orderOf y = 2 → y ∉ J →
      QuotientGroup.mk' J y = QuotientGroup.mk' J x ∨
        QuotientGroup.mk' J y = (QuotientGroup.mk' J x) ^ 2 := by
  intro H J x y hx hy hxJ hy2 hyJ
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let model := e.toMonoidHom.comp q
  let A := (d.localSylow : Subgroup H).map model
  obtain ⟨hcyc, hcard⟩ := SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A
    (d.localSylow.isPGroup'.map model)
  let : IsCyclic A := hcyc
  have hmem (u : H) (hu : (u : G) ∈ (d.sylow : Subgroup G)) : model u ∈ A := by
    rw [d.sylow_map] at hu
    obtain ⟨v, hv, heq⟩ := hu
    exact mem_map_of_mem model ((H.subtype_injective heq) ▸ hv)
  let xA : A := ⟨model x, hmem x hx⟩
  let yA : A := ⟨model y, hmem y hy⟩
  have hne (u : H) (hu : u ∉ J) : model u ≠ 1 := by
    intro heq
    exact hu ((QuotientGroup.eq_one_iff u).mp
      (e.injective (heq.trans (map_one e).symm)))
  have hyA : orderOf yA = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      change model y ^ 2 = 1
      rw [← map_pow, show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y, map_one]
    · exact fun hh => hne y hyJ (congrArg A.subtype hh)
  have hxord : orderOf xA = 2 ∨ orderOf xA = 4 := by
    have hd := (orderOf_dvd_natCard xA).trans hcard
    have hh : orderOf xA ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h1 | h2 | h4
    · exact (hne x hxJ (congrArg A.subtype (orderOf_eq_one_iff.mp h1))).elim
    · exact Or.inl h2
    · exact Or.inr h4
  rcases hxord with hx2 | hx4
  · left
    exact e.injective (congrArg A.subtype (IsCyclic.eq_of_orderOf_eq_two hyA hx2))
  · right
    have hx22 : orderOf (xA ^ 2) = 2 := by rw [orderOf_pow, hx4]; decide
    have hh := congrArg A.subtype (IsCyclic.eq_of_orderOf_eq_two hyA hx22)
    apply e.injective
    change e (q y) = e (q x) ^ 2 at hh
    simpa only [map_pow] using hh

/-- Outside the original two-core, every element of the supplied Sylow
subgroup fixes only points of E lying in the omega center. -/
public theorem sylow_outer_derived_fixed_le_omega_center
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∀ x : G, x ∈ (d.sylow : Subgroup G) → x ∉ J.map H.subtype →
      E ⊓ centralizer ({x} : Set G) ≤ ZU := by
  intro H J E N K U ZU x hx hxJ
  let D := commutator J
  let Z := (center J).subgroupOf D
  let i := H.subtype.comp J.subtype
  let embed := i.comp D.subtype
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' Z
  obtain ⟨f, hf, hformula⟩ := parrott_derived_quotient_action z h
  obtain ⟨y, hyK, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core h hN hproper
  let xH : H := ⟨x, d.sylow_le_centralizer hx⟩
  let yH : H := ⟨y, d.sylow_le_centralizer (d.normalizer_core_le_sylow hyK)⟩
  have hxHJ : xH ∉ J := fun hh => hxJ (mem_map_of_mem H.subtype hh)
  have hyHJ : yH ∉ J := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hyH2 : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy2
  let S := (FixedPoints.subgroup (zpowers (f (qJ yH))) (D ⧸ Z)).comap qD
  have hScard : Nat.card S = 8 := quotient_fixed_card z h f hf yH hyH2 hyHJ
  have hinj : Function.Injective embed :=
    (H.subtype_injective.comp J.subtype_injective).comp D.subtype_injective
  have hZUcard : Nat.card ZU = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hZUE : ZU ≤ E := (d.normalizer_core_omega_structure h hN hproper).2.2.1.trans
    inf_le_left
  have hyU : y ∈ U.map (N.subtype.comp K.subtype) := by
    obtain ⟨yN, hyN, rfl⟩ := hyK
    let yK : K := ⟨yN, hyN⟩
    refine ⟨yK, subset_closure ?_, rfl⟩
    change yK ^ (2 ^ 1) = 1
    apply (N.subtype_injective.comp K.subtype_injective)
    change (yN : G) ^ (2 ^ 1) = 1
    simpa only [pow_one] using hy2 ▸ pow_orderOf_eq_one (yN : G)
  have hZUy : ZU ≤ centralizer ({y} : Set G) := by
    rintro a ⟨aU, haU, rfl⟩
    obtain ⟨yK, hyKU, heq⟩ := hyU
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg ((N.subtype.comp K.subtype).comp U.subtype)
      (mem_center_iff.mp haU ⟨yK, hyKU⟩)
    change (N.subtype.comp K.subtype) yK *
      ((N.subtype.comp K.subtype).comp U.subtype) aU =
      ((N.subtype.comp K.subtype).comp U.subtype) aU *
      (N.subtype.comp K.subtype) yK at hh
    rw [heq] at hh
    exact hh.symm
  have hfix (a : H) (v : D) (hv : embed v ∈ centralizer ({(a : G)} : Set G)) :
      f (qJ a) (qD v) = qD v := by
    apply hformula a v v
    apply H.subtype_injective
    change embed v = (a : G) * embed v * (a : G)⁻¹
    exact (mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp hv).symm).symm
  have hZUS : ZU = S.map embed := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective hinj, hScard, hZUcard])
    intro a ha
    obtain ⟨aJ, haD, heq⟩ := hZUE ha
    let aD : D := ⟨aJ, haD⟩
    refine ⟨aD, ?_, heq⟩
    change qD aD ∈ FixedPoints.subgroup (zpowers (f (qJ yH))) (D ⧸ Z)
    apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
    apply hfix yH aD
    change i aJ ∈ centralizer ({y} : Set G)
    rw [heq]
    exact hZUy ha
  intro w hw
  obtain ⟨wJ, hwD, heq⟩ := hw.1
  let wD : D := ⟨wJ, hwD⟩
  have hfx : f (qJ xH) (qD wD) = qD wD := hfix xH wD (by
    change i wJ ∈ centralizer ({x} : Set G)
    rw [heq]
    exact hw.2)
  rw [hZUS]
  refine ⟨wD, ?_, heq⟩
  change qD wD ∈ FixedPoints.subgroup (zpowers (f (qJ yH))) (D ⧸ Z)
  apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
  rcases d.quotient_involution_eq_or_square h xH yH hx
    (d.normalizer_core_le_sylow hyK) hxHJ hyH2 hyHJ with he | he
  · rw [he]
    exact hfx
  · rw [he, map_pow]
    change f (qJ xH) (f (qJ xH) (qD wD)) = qD wD
    rw [hfx, hfx]

/-- For a point of E∩F outside the omega center, the centralizer in the
second normalizer is exactly its centralizer in the original two-core. -/
public theorem normalizer_elementary_outside_omega_center_centralizer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∀ w : G, w ∈ E ⊓ d.F → w ∉ ZU →
      N ⊓ centralizer ({w} : Set G) =
        J.map H.subtype ⊓ centralizer ({w} : Set G) := by
  intro H J E N K U ZU w hw hwZ
  let C := N ⊓ centralizer ({w} : Set G)
  let B := E ⊓ d.F
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hZB : ZU ≤ B := (d.normalizer_core_omega_structure h hN hproper).2.2.1
  have hZcard : Nat.card ZU = 8 :=
    (card_map_of_injective ((N.subtype_injective.comp K.subtype_injective).comp
      U.subtype_injective)).trans (d.normalizer_core_omega_structure h hN hproper).2.1
  have hspan : ZU ⊔ zpowers w = B := by
    apply eq_of_le_of_card_ge (sup_le hZB (zpowers_le.mpr hw))
    rw [card_sup_zpowers_of_normalizing_involution ZU w
      (elemPow_eq_one_of_isElementaryAbelian w hw.2) hwZ
      (d.normalizer_core_centers_normalized.2 (d.sylow_le_normalizer (d.le_sylow hw.2))),
      hZcard, show Nat.card B = 16 from d.inf_card]
  have hCB : C ≤ normalizer (B : Set G) := by
    rw [← hspan]
    apply le_trans (le_inf (inf_le_left.trans d.normalizer_core_centers_normalized.2) ?_)
      (normalizer_inf_normalizer_le_normalizer_sup ZU (zpowers w))
    apply le_trans (show C ≤ centralizer (zpowers w : Set G) from ?_)
      (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure, centralizer_closure]
    exact inf_le_right
  have hCjoin : C ≤ normalizer ((E ⊔ d.F : Subgroup G) : Set G) := by
    rw [← d.elementary_inf_centralizer h]
    exact hCB.trans (normalizer_le_normalizer_centralizer B)
  have hCH : C ≤ H := hCjoin.trans
    (normalizer_le_centralizer_of_characteristic_involution
      (E ⊔ d.F) (commutator (E ⊔ d.F : Subgroup G)) z h.involution
      (d.elementary_join_commutator h))
  have hCT : C ≤ (d.sylow : Subgroup G) := by
    rw [← d.normalizer_inf_centralizer h]
    exact le_inf inf_le_left hCH
  apply le_antisymm ?_ (inf_le_inf_right _ (d.core_le_sylow.trans d.sylow_le_normalizer))
  intro x hx
  refine ⟨?_, hx.2⟩
  by_contra hxJ
  apply hwZ
  apply d.sylow_outer_derived_fixed_le_omega_center h hN hproper x (hCT hx) hxJ
  exact ⟨hw.1, mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp hx.2).symm⟩

/-- The normalizer centralizer of every point in (E∩F)−Z(Ω₁(K))
has order 256, before any orbit or fusion calculation. -/
public theorem normalizer_elementary_outside_omega_center_centralizer_card
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    ∀ w : G, w ∈ E ⊓ d.F → w ∉ ZU →
      Nat.card (N ⊓ centralizer ({w} : Set G) : Subgroup G) = 256 := by
  intro H J E N K U ZU w hw hwZ
  rw [d.normalizer_elementary_outside_omega_center_centralizer h hN hproper w hw hwZ]
  apply parrott_derived_core_centralizer_card z h w hw.1
  exact fun hh => hwZ ((zpowers_le.mpr
    (d.normalizer_core_omega_inclusions.2.1 d.z_mem_normalizer_core_center)) hh)

end ParrottSecondElementaryData
end Stellmacher.Recognition
