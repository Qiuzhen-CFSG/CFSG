module
public import Stellmacher.Recognition.Parrott.DerivedQuotientAction
public import Theory.GroupAction.FiveInvertingInvolutionFixed
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolution

/-!
# The fixed subgroup of an outer involution on Parrott's derived subgroup

Under the original Parrott centralizer hypotheses, put H=C_G(z),
J=O₂(H), and let E be the actual image of J′ in G. Every involution of H
outside J centralizes exactly eight elements of E. More generally, any
element outside J whose square lies in J centralizes at most eight elements
of E. No simplicity or N₂ hypothesis is needed for these local statements.

Work first with D=J′ and Z=Z(J) intersected with D. The first centralizer
lemma gives D elementary of order32, Z of order2, and D/Z of order16.
The actual faithful action of H/J on D/Z identifies the outer involution
with an automorphism inverting an order5 automorphism, by the supplied
faithful C5 semidirect C4 model. The reflection fixed-space theorem gives
four fixed elements in D/Z. This only requires the image in H/J to be an
involution. Restricting the quotient map to fixed elements of D therefore
bounds their number by2·4=8. For an actual involution, the displacement
bound gives the reverse square bound, and divisibility by32 forces eight.
An explicit bijection transports these fixed elements to C_E(y) in G.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), pp.674–675, the fixed-space calculation immediately before
Lemma 3. The proof uses the literal core, derived subgroup, conjugation
formula, and ambient embedding throughout.
-/

open Subgroup
open scoped IsMulCommutative

private theorem fixed_zpowers_mem {V : Type*} [Group V] (a : MulAut V) (v : V) :
    v ∈ FixedPoints.subgroup (zpowers a) V ↔ a v = v := by
  constructor
  · intro hv
    exact hv ⟨a, mem_zpowers a⟩
  · intro hv g
    obtain ⟨n, hn⟩ := g.property
    change (g : MulAut V) v = v
    rw [← hn]
    exact MulAction.mem_fixedBy_zpow (show v ∈ MulAction.fixedBy V a from hv) n

namespace Stellmacher.Recognition

private theorem outer_fixed_card_data {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ y : H, y ^ 2 ∈ J → y ∉ J →
      Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) ≤ 8 ∧
      (y ^ 2 = 1 → Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) = 8) := by
  classical
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let Z := (center J).subgroupOf D
  let E := D.map (H.subtype.comp J.subtype)
  let W := D ⧸ Z
  let qJ := QuotientGroup.mk' J
  let qD := QuotientGroup.mk' Z
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have haction : ∃ f : (H ⧸ J) →* MulAut W, Function.Injective f ∧
      ∀ a : H, ∀ d d' : D, ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
        f (qJ a) (qD d) = qD d' := parrott_derived_quotient_action z h
  change ∀ y : H, y ^ 2 ∈ J → y ∉ J →
      Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) ≤ 8 ∧
      (y ^ 2 = 1 → Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) = 8)
  obtain ⟨f, hf, hformula⟩ := haction
  intro y hy2J hyJ
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
  let Y := zpowers y
  let : MulDistribMulAction Y J := conjMulDistribMulActionOfLeNormalizer Y J
    (le_normalizer_of_normal (H := J))
  let : IsInvariant Y J D := isInvariant_of_characteristic D
  let yY : Y := ⟨y, mem_zpowers y⟩
  let bD : MulAut D := MulDistribMulAction.toMulAut Y D yY
  have hcompat (d : D) : b (qD d) = qD (bD d) := hformula y d (bD d) rfl
  let C := FixedPoints.subgroup (zpowers bD) D
  let θ : C →* W := qD.comp C.subtype
  have hkerBound : Nat.card θ.ker ≤ 2 := by
    let i : θ.ker → Z := fun x => ⟨(x : C), (QuotientGroup.eq_one_iff (x : D)).mp x.property⟩
    have hi : Function.Injective i := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : Z => (a : D)) hxy
    exact (Nat.card_le_card_of_injective i hi).trans_eq hZcard
  have hrange : θ.range ≤ FixedPoints.subgroup (zpowers b) W := by
    rintro w ⟨d, rfl⟩
    apply (fixed_zpowers_mem b _).mpr
    change b (qD (d : D)) = qD (d : D)
    rw [hcompat, (fixed_zpowers_mem bD _).mp d.property]
  have hrangeBound : Nat.card θ.range ≤ 4 := (card_le_of_le hrange).trans_eq hfixedW
  have hCupper : Nat.card C ≤ 8 := by
    have hh := θ.ker.card_mul_index
    rw [index_ker] at hh
    nlinarith only [hh, hkerBound, hrangeBound]
  have hCcard (hy2 : y ^ 2 = 1) : Nat.card C = 8 := by
    have hyY2 : yY ^ 2 = 1 := Subtype.ext hy2
    have hbD2 : bD ^ 2 = 1 := by
      dsimp [bD]
      rw [← map_pow, hyY2, map_one]
    have hClower : 32 ≤ Nat.card C * Nat.card C := by
      obtain ⟨hh, hle⟩ := MulAut.involution_fixed_displacement_card_data bD hbD2
      change Nat.card D = Nat.card C * _ at hh
      rw [← hDcard, hh]
      exact Nat.mul_le_mul_left _ (card_le_of_le hle)
    have hCcard : Nat.card C = 8 := by
      have hd : Nat.card C ∣ 2 ^ 5 := by simpa [hDcard] using C.card_subgroup_dvd_card
      obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      rw [hc] at hCupper hClower ⊢
      interval_cases n <;> omega
    exact hCcard
  let B := (centralizer ({(y : G)} : Set G)).subgroupOf E
  let embed : D →* G := (H.subtype.comp J.subtype).comp D.subtype
  have hfix_iff (d : D) : d ∈ C ↔ embed d ∈ centralizer ({(y : G)} : Set G) := by
    rw [fixed_zpowers_mem, mem_centralizer_singleton_iff]
    constructor
    · intro hd
      have hh := congrArg embed hd
      change (y : G) * embed d * (y : G)⁻¹ = embed d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hd
      apply Subtype.ext
      apply Subtype.ext
      apply H.subtype_injective
      change (y : G) * embed d * (y : G)⁻¹ = embed d
      exact mul_inv_eq_iff_eq_mul.mpr hd.symm
  let i : C → B := fun d => ⟨⟨embed d, mem_map_of_mem (H.subtype.comp J.subtype)
      d.val.property⟩, (hfix_iff d).mp d.property⟩
  have hi : Function.Bijective i := by
    constructor
    · intro d d' heq
      apply Subtype.ext
      apply Subtype.ext
      apply J.subtype_injective
      apply H.subtype_injective
      exact congrArg (fun x : B => ((x : E) : G)) heq
    · intro c
      obtain ⟨d, hd, hdc⟩ := (c : E).property
      let dD : D := ⟨d, hd⟩
      have hdC : dD ∈ C := by
        apply (hfix_iff dD).mpr
        have hdc' : embed dD = ((c : E) : G) := hdc
        rw [hdc']
        exact c.property
      exact ⟨⟨dD, hdC⟩, Subtype.ext (Subtype.ext hdc)⟩
  have hc := (Nat.card_congr (Equiv.ofBijective i hi)).symm
  exact ⟨hc.le.trans hCupper, fun hy2 => hc.trans (hCcard hy2)⟩

/-- An element outside the core whose square lies in the core fixes at most
eight elements of the actual derived image. No order condition on the element
itself is required. -/
public theorem parrott_outer_square_mem_core_fixed_card_le
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ y : H, y ^ 2 ∈ J → y ∉ J →
      Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) ≤ 8 := by
  intro H J E y hy hyJ
  exact (outer_fixed_card_data z h y hy hyJ).1

/-- An involution outside the two-core fixes eight elements of the actual derived image. -/
public theorem parrott_outer_involution_fixed_card {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ y : H, orderOf y = 2 → y ∉ J →
      Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) = 8 := by
  intro H J E y hy hyJ
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  exact (outer_fixed_card_data z h y (hy2 ▸ J.one_mem) hyJ).2 hy2

end Stellmacher.Recognition
