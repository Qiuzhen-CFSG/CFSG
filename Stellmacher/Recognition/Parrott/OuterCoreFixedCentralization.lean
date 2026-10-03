module

public import Stellmacher.Recognition.Parrott.OuterInvolutionFixedSpace
public import Theory.GroupAction.FullRankInvolutionCentralKernel

/-!
# Core centralization of the fixed derived subgroup

If y is an involution of H=C_G(z) outside J=O₂(H), every x in J with
[x,y] in J′ centralizes C_{J′}(y). In particular this holds for C_J(y).
The actions of x and y on the abelian J′ commute. On D=J′, conjugation by x is
trivial modulo Z(J), and H fixes Z(J) pointwise. The y-action on D/Z(J)
has four fixed points in a group of order sixteen, so its fixed subgroup
is its displacement subgroup. The commuting-automorphism lemma then
lifts pointwise fixation to C_D(y).

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.674–676, the local structure used in the outer omega calculation.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace Stellmacher.Recognition

/-- A core element whose commutator with an outer involution lies in the
derived core centralizes the fixed subgroup of that involution in the derived core. -/
public theorem parrott_outer_core_centralizes_derived_fixed_of_commutator_mem
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    ∀ y : H, orderOf y = 2 → y ∉ J →
      ∀ x : H, x ∈ J → ⁅x, y⁆ ∈ DH →
        ∀ d : H, d ∈ DH → Commute d y → Commute x d := by
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
  change ∀ y : H, orderOf y = 2 → y ∉ J → _
  obtain ⟨f, hf, hformula⟩ := haction
  intro y hy hyJ x hxJ hxy
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
  let ι : H →* normalizer (J : Set H) :=
    (MonoidHom.id H).codRestrict _ (by intro u; rw [normalizer_eq_top]; trivial)
  let jAct : H →* MulAut J := J.normalizerMonoidHom.comp ι
  let : MulDistribMulAction H J := MulDistribMulAction.compHom J jAct
  let : IsInvariant H J D := isInvariant_of_characteristic D
  let action : H →* MulAut D := MulDistribMulAction.toMulAut H D
  have hcompat (d : D) : qD (action y d) = b (qD d) :=
    (hformula y d (action y d) rfl).symm
  have hxquot (d : D) : qD (action x d) = qD d := by
    rw [← hformula x d (action x d) rfl]
    have hqx : qJ x = 1 := (QuotientGroup.eq_one_iff x).mpr hxJ
    rw [hqx, map_one]
    rfl
  have hkerFixed (u : H) (d : D) (hd : d ∈ qD.ker) : action u d = d := by
    have hdZ : (d : J) ∈ center J := (QuotientGroup.eq_one_iff d).mp hd
    have hdG : (((d : J) : H) : G) ∈ zpowers z :=
      hZmap ▸ mem_map_of_mem (H.subtype.comp J.subtype) hdZ
    have huC : (u : G) ∈ centralizer (zpowers z : Set G) := by
      intro v hv
      obtain ⟨n, rfl⟩ := hv
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp u.property : Commute (u : G) z) n).symm.eq
    apply Subtype.ext
    apply Subtype.ext
    apply H.subtype_injective
    change (u : G) * (((d : J) : H) : G) * (u : G)⁻¹ = (((d : J) : H) : G)
    exact mul_inv_eq_iff_eq_mul.mpr (huC _ hdG).symm
  have hactions : Commute (action x) (action y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    obtain ⟨c, hc, heq⟩ := hxy
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    change ⁅x, y⁆ * ((v : J) : H) * ⁅x, y⁆⁻¹ = ((v : J) : H)
    rw [← heq]
    exact congrArg J.subtype (mul_inv_eq_iff_eq_mul.mpr
      (congrArg D.subtype (mul_comm (⟨c, hc⟩ : D) v)))
  have hfix := MulAut.fixes_fixedPoints_of_commute_of_full_rank_quotient
    qD (QuotientGroup.mk'_surjective Z) (action x) (action y) b hcompat hb2
    (by rw [hWcard, hfixedW]; rfl) hactions hxquot (hkerFixed x) (hkerFixed y)
  intro d hd hdy
  obtain ⟨d, hd, rfl⟩ := hd
  let dD : D := ⟨d, hd⟩
  have hyd : action y dD = dD := by
    apply Subtype.ext
    apply Subtype.ext
    change y * (d : H) * y⁻¹ = (d : H)
    exact mul_inv_eq_iff_eq_mul.mpr hdy.symm.eq
  have hxd := congrArg (fun v : D => ((v : J) : H)) (hfix dD hyd)
  change x * (d : H) * x⁻¹ = (d : H) at hxd
  exact mul_inv_eq_iff_eq_mul.mp hxd

/-- Core elements commuting with an outer involution centralize its fixed
subgroup in the derived core. The core element need not be an involution. -/
public theorem parrott_outer_core_centralizes_derived_fixed
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let DH := (commutator J).map J.subtype
    ∀ y : H, orderOf y = 2 → y ∉ J →
      ∀ x : H, x ∈ J → Commute x y →
        ∀ d : H, d ∈ DH → Commute d y → Commute x d := by
  intro H J DH y hy hyJ x hx hxy
  exact parrott_outer_core_centralizes_derived_fixed_of_commutator_mem z h y hy hyJ
    x hx (hxy.commutator_eq ▸ DH.one_mem)

end Stellmacher.Recognition
