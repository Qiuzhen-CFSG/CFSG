module
public import Stellmacher.Recognition.Parrott.OuterInvolutionFixedSpace
public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup

/-!
# Fixed points of outer elements of quotient order four

Under Parrott's original centralizer hypotheses, write H=C_G(z),
J=O₂(H), and E for the actual ambient image of J′. An element whose
image in H/J has order four fixes at most four elements of E.

The faithful action on J′/Z(J) has order four. Its square has four fixed
points by the five-inverting involution calculation. Squaring strictly
enlarges the fixed subgroup, so the order-four action fixes at most two
points of this quotient. The central kernel has order two, giving the
claimed bound on E.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
p.674, Sylow action preceding Lemma 3.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition

/-- The faithful derived central quotient action of a quotient-order-four
actor has at most two fixed points. -/
public theorem parrott_derived_quotient_four_fixed_card_le
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let D := commutator J
    let Z := (center J).subgroupOf D
    ∀ f : (H ⧸ J) →* MulAut (D ⧸ Z), Function.Injective f →
      ∀ y : H, orderOf (QuotientGroup.mk' J y) = 4 →
        Nat.card (FixedPoints.subgroup (zpowers (f (QuotientGroup.mk' J y)))
          (D ⧸ Z)) ≤ 2 := by
  classical
  intro H J D Z f hf y hy
  let W := D ⧸ Z
  let qJ := QuotientGroup.mk' J
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
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
  have hbOrder : orderOf b = 4 := (orderOf_injective f hf (qJ y)).trans hy
  have hb4 : b ^ 4 = 1 := hbOrder ▸ pow_orderOf_eq_one b
  have hbne : b ≠ 1 := by
    intro heq
    simp only [heq, orderOf_one] at hbOrder
    omega
  have hb22 : (b ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hb4
  have hybar2 : orderOf (e ((qJ y) ^ 2)) = 2 := by
    rw [e.orderOf_eq, orderOf_pow, hy]
    decide
  have hab : b ^ 2 * a * (b ^ 2)⁻¹ = a⁻¹ := by
    have hh := congrArg g (faithful_five_four_involution_inverts_left φ hφ
      (e ((qJ y) ^ 2)) hybar2 u)
    have hgy : g (e ((qJ y) ^ 2)) = b ^ 2 := by
      simp only [g, b, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        e.symm_apply_apply, map_pow]
    have hgyinv : g ((e ((qJ y) ^ 2))⁻¹) = (b ^ 2)⁻¹ :=
      (map_inv g _).trans (congrArg Inv.inv hgy)
    have hright : g (SemidirectProduct.inl u⁻¹) = a⁻¹ :=
      (g.comp SemidirectProduct.inl).map_inv u
    rw [map_mul, map_mul, hgy, hgyinv, hright] at hh
    exact hh
  have hfixedW2 : Nat.card (FixedPoints.subgroup (zpowers (b ^ 2)) W) = 4 :=
    card_fixed_of_involution_inverting_five_on_sixteen hWcard a (b ^ 2) ha hb22 hab
  have hfixedW : Nat.card (FixedPoints.subgroup (zpowers b) W) ≤ 2 := by
    have hlt := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one b hb4 hbne
    rw [hfixedW2] at hlt
    have hd : Nat.card (FixedPoints.subgroup (zpowers b) W) ∣ 2 ^ 4 := by
      simpa [hWcard] using
        (FixedPoints.subgroup (zpowers b) W).card_subgroup_dvd_card
    obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rw [hc] at hlt ⊢
    interval_cases n <;> omega
  exact hfixedW

/-- An element of quotient order four centralizes at most four elements of
the actual derived image of the two-core. -/
public theorem parrott_outer_four_fixed_card_le
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ y : H, orderOf (QuotientGroup.mk' J y) = 4 →
      Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) ≤ 4 := by
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
  change ∀ y : H, orderOf (qJ y) = 4 →
      Nat.card ((centralizer ({(y : G)} : Set G)).subgroupOf E) ≤ 4
  obtain ⟨f, hf, hformula⟩ := haction
  intro y hy
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
  let b : MulAut W := f (qJ y)
  have hfixedW : Nat.card (FixedPoints.subgroup (zpowers b) W) ≤ 2 :=
    parrott_derived_quotient_four_fixed_card_le z h f hf y hy
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
    apply (MulAut.mem_fixed_zpowers_iff b _).mpr
    change b (qD (d : D)) = qD (d : D)
    rw [hcompat, (MulAut.mem_fixed_zpowers_iff bD _).mp d.property]
  have hrangeBound : Nat.card θ.range ≤ 2 := (card_le_of_le hrange).trans hfixedW
  have hCupper : Nat.card C ≤ 4 := by
    have hh := θ.ker.card_mul_index
    rw [index_ker] at hh
    nlinarith only [hh, hkerBound, hrangeBound]
  let B := (centralizer ({(y : G)} : Set G)).subgroupOf E
  let embed : D →* G := (H.subtype.comp J.subtype).comp D.subtype
  have hfix_iff (d : D) : d ∈ C ↔ embed d ∈ centralizer ({(y : G)} : Set G) := by
    rw [MulAut.mem_fixed_zpowers_iff, mem_centralizer_singleton_iff]
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
  exact hc.le.trans hCupper


/-- A two-subgroup centralizing at least eight elements of the derived image
has image of order at most two modulo the core. -/
public theorem parrott_two_subgroup_centralizer_relIndex_le_two
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ X U : Subgroup G, X ≤ H → IsPGroup 2 X → U ≤ E →
      8 ≤ Nat.card U → X ≤ centralizer (U : Set G) →
        (J.map H.subtype).relIndex X ≤ 2 := by
  classical
  intro H J E X U hXH hXtwo hUE hU hXU
  let K := X.subgroupOf H
  let q := QuotientGroup.mk' J
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let model := e.toMonoidHom.comp q
  let A := K.map model
  have hKtwo : IsPGroup 2 K := hXtwo.of_injective
    (subgroupOfEquivOfLe hXH).toMonoidHom (subgroupOfEquivOfLe hXH).injective
  obtain ⟨hcyc, hdiv⟩ :=
    SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ A (hKtwo.map model)
  let _ : IsCyclic A := hcyc
  have hrel : (J.map H.subtype).relIndex X = Nat.card A := by
    calc
      _ = (J.map H.subtype).relIndex (K.map H.subtype) := by
        rw [map_subgroupOf_eq_of_le hXH]
      _ = J.relIndex K := relIndex_map_map_of_injective J K H.subtype_injective
      _ = Nat.card (K.map q) := by
        have hh := relIndex_ker K q
        rw [QuotientGroup.ker_mk'] at hh
        exact hh
      _ = Nat.card A := by
        have hh := card_map_of_injective (K := K.map q)
          (f := e.toMonoidHom) e.injective
        rw [map_map] at hh
        exact hh.symm
  rw [hrel]
  have hchoices : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 4 := by
    have hh : Nat.card A ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hh
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  rcases hchoices with hcard | hcard | hcard
  · omega
  · omega
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  rw [hcard] at ha
  obtain ⟨y, hyK, hya⟩ := a.property
  have hyOrder : orderOf (q y) = 4 := by
    have hh : orderOf (model y) = 4 := by
      rw [hya]
      exact (orderOf_injective A.subtype A.subtype_injective a).trans ha
    simpa only [model, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.orderOf_eq] using hh
  have hbound := parrott_outer_four_fixed_card_le z h y hyOrder
  let C := (centralizer ({(y : G)} : Set G)).subgroupOf E
  have hUC : U ≤ centralizer ({(y : G)} : Set G) := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact mem_centralizer_iff.mp (hXU hyK) u hu
  let i : U → C := fun u => ⟨⟨(u : G), hUE u.property⟩, hUC u.property⟩
  have hi : Function.Injective i := by
    intro u v huv
    exact Subtype.ext (congrArg (fun c : C => ((c : E) : G)) huv)
  have hle : Nat.card U ≤ Nat.card C := Nat.card_le_card_of_injective i hi
  change Nat.card C ≤ 4 at hbound
  omega

/-- Sylow-local form of the counting bound used in the normalizer-center
assembly: a subgroup centralizing an eight-element subgroup of E meets the
mapped core in index at most two. -/
public theorem parrott_sylow_centralizer_relIndex_le_two
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∀ S : Sylow 2 H,
    let T := (S : Subgroup H).map H.subtype
    ∀ X U : Subgroup G, X ≤ T → U ≤ E → 8 ≤ Nat.card U →
      X ≤ centralizer (U : Set G) → (J.map H.subtype).relIndex X ≤ 2 := by
  intro H J E S T X U hXT hUE hU hXU
  have hTH : T ≤ H := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  exact parrott_two_subgroup_centralizer_relIndex_le_two z h X U
    (hXT.trans hTH) ((S.isPGroup'.map H.subtype).to_le hXT) hUE hU hXU

end Stellmacher.Recognition
