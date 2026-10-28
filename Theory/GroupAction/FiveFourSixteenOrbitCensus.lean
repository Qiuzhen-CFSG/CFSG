module
public import Theory.GroupAction.FiveFourSixteenOrbits
public import Theory.GroupAction.FiveTenOrbitCounting
public import Theory.GroupAction.FiveInvertingInvolutionFixed
public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolution

/-!
# The two nonidentity orbits of a faithful five-four action on sixteen

A faithful action of C₅ ⋊ C₄ on an elementary abelian group of order sixteen,
with faithful action of C₄ on C₅, has nonidentity orbits of sizes five and ten.
The orbits below are the evaluation orbits of the supplied homomorphism.

The square of a generator of C₄ inverts C₅ and hence fixes four vectors.
The generator itself fixes strictly fewer; its fixed subgroup therefore has
at most two elements. Every nonidentity orbit has size divisible by five.
The general five-and-ten counting lemma now applies: the unique nonidentity
C₄-fixed vector belongs to every five-element orbit, excluding three such
orbits.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674. No classification of actions or chosen orbit representatives is
assumed.
-/

namespace Theory.GroupAction
open Subgroup MulAction

private abbrev C5 := Multiplicative (ZMod 5)
private abbrev C4 := Multiplicative (ZMod 4)

/-- A faithful five-four action on elementary sixteen has exactly a five-point
and a ten-point orbit outside the identity. -/
public theorem five_four_sixteen_orbit_census
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f) :
    ∃ x y : V, x ≠ 1 ∧ y ≠ 1 ∧
      (Set.range (fun g => f g x)).ncard = 5 ∧
      (Set.range (fun g => f g y)).ncard = 10 ∧
      ∀ w : V, w ≠ 1 →
        w ∈ Set.range (fun g => f g x) ∪ Set.range (fun g => f g y) := by
  let M := SemidirectProduct C5 C4 φ
  let : Finite M := Finite.of_equiv (C5 × C4) SemidirectProduct.equivProd.symm
  let : MulDistribMulAction M V := MulDistribMulAction.compHom V f
  let i : C4 →* M := SemidirectProduct.inr
  have hi : Function.Injective i := SemidirectProduct.inr_injective
  have hC5 : Nat.card C5 = 5 := by change Nat.card (ZMod 5) = 5; simp
  have hC4 : Nat.card C4 = 4 := by change Nat.card (ZMod 4) = 4; simp
  have hM : Nat.card M = 20 := by rw [SemidirectProduct.card, hC5, hC4]
  have hfixed : letI := MulDistribMulAction.compHom V i
      Nat.card (FixedPoints.subgroup C4 V) ≤ 2 := by
    let : MulDistribMulAction C4 V := MulDistribMulAction.compHom V i
    let c : C4 := Multiplicative.ofAdd (1 : ZMod 4)
    let d : C5 := Multiplicative.ofAdd (1 : ZMod 5)
    let a : MulAut V := f (SemidirectProduct.inl d)
    let b : MulAut V := f (i c)
    have hc : orderOf c = 4 := by simp [c, orderOf_ofAdd_eq_addOrderOf]
    have hd : orderOf d = 5 := by simp [d, orderOf_ofAdd_eq_addOrderOf]
    have ha : orderOf a = 5 := by
      rw [orderOf_injective f hf,
        orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective, hd]
    have hb : orderOf b = 4 := by
      rw [orderOf_injective f hf, orderOf_injective i hi, hc]
    have hb4 : b ^ 4 = 1 := hb ▸ pow_orderOf_eq_one b
    have hbne : b ≠ 1 := by intro h; simp [h] at hb
    have hsquare : orderOf ((i c) ^ 2) = 2 := by
      rw [orderOf_pow, orderOf_injective i hi, hc]
      decide
    have hinverts : b ^ 2 * a * (b ^ 2)⁻¹ = a⁻¹ := by
      have hh := congrArg f
        (faithful_five_four_involution_inverts_left φ hφ ((i c) ^ 2) hsquare d)
      simpa only [map_mul, map_pow, map_inv] using hh
    have hb22 : (b ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hb4
    have hFsquare := card_fixed_of_involution_inverting_five_on_sixteen
      hV a (b ^ 2) ha hb22 hinverts
    have hFlt := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one b hb4 hbne
    rw [hFsquare] at hFlt
    have hFnot3 : Nat.card (FixedPoints.subgroup (zpowers b) V) ≠ 3 := by
      intro h3
      have hdiv := (FixedPoints.subgroup (zpowers b) V).card_subgroup_dvd_card
      rw [h3, hV] at hdiv
      norm_num at hdiv
    have hle : FixedPoints.subgroup C4 V ≤ FixedPoints.subgroup (zpowers b) V := by
      intro v hv
      exact (MulAut.mem_fixed_zpowers_iff b v).mpr (hv c)
    have hcard := card_le_of_le hle
    omega
  exact five_ten_orbit_census_of_fixed_card_le_two hM hC4 hV i hi
    (fun v hv => five_dvd_orbit_card_of_faithful_five_four_action hV φ f hf v hv) hfixed

end Theory.GroupAction
