module

public import Theory.GroupAction.FiveInvertingInvolutionFixed
public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolutionCentralizer

/-!
# Involution-fixed points in five-point orbits

In a faithful action of C₅⋊C₄ on elementary sixteen, an involution fixes
at most one nonidentity vector whose orbit has size five. Such a vector
has a cyclic stabilizer of order four containing the involution, hence
its stabilizer is the involution's centralizer. A generator of that
centralizer fixes at most two vectors: its square fixes four and squaring
strictly enlarges the fixed subgroup.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.674, the two orbits in J/J′.
-/

namespace Theory.GroupAction
open Subgroup MulAction
open scoped IsMulCommutative

/-- Among nonidentity vectors in five-point orbits, an involution has at
most one fixed point in a faithful five-four action on elementary sixteen. -/
public theorem five_four_involution_fixed_five_orbit_unique
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ →*
      MulAut V) (hf : Function.Injective f)
    (u : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
    (hu : orderOf u = 2)
    (v w : V) (hv : v ≠ 1) (hw : w ≠ 1)
    (hv5 : (Set.range (fun g => f g v)).ncard = 5)
    (hw5 : (Set.range (fun g => f g w)).ncard = 5)
    (huv : f u v = v) (huw : f u w = w) : v = w := by
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let : MulDistribMulAction M V := MulDistribMulAction.compHom V f
  have hM : Nat.card M = 20 := by rw [SemidirectProduct.card]; norm_num
  let C := centralizer ({u} : Set M)
  obtain ⟨hCcyc, hCcard⟩ := faithful_five_four_involution_centralizer φ hφ u hu
  let : IsCyclic C := hCcyc
  obtain ⟨r, hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hCcyc
  have hr4 : orderOf r = 4 := hr.trans hCcard
  let b : MulAut V := f (r : M)
  have hb : orderOf b = 4 := by
    rw [orderOf_injective f hf, Subgroup.orderOf_coe]
    exact hr4
  have hb4 : b ^ 4 = 1 := hb ▸ pow_orderOf_eq_one b
  have hbne : b ≠ 1 := by intro hh; simp [hh] at hb
  let t : Multiplicative (ZMod 5) := Multiplicative.ofAdd 1
  let a : MulAut V := f (SemidirectProduct.inl t)
  have ht : orderOf t = 5 := by simp [t, orderOf_ofAdd_eq_addOrderOf]
  have ha : orderOf a = 5 := by
    rw [orderOf_injective f hf,
      orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective]
    exact ht
  have hrSquare : orderOf ((r : M) ^ 2) = 2 := by
    rw [orderOf_pow, Subgroup.orderOf_coe, hr4]
    decide
  have hinv : b ^ 2 * a * (b ^ 2)⁻¹ = a⁻¹ := by
    have hh := congrArg f
      (faithful_five_four_involution_inverts_left φ hφ ((r : M) ^ 2) hrSquare t)
    simpa only [map_mul, map_pow, map_inv] using hh
  have hfixedSquare := card_fixed_of_involution_inverting_five_on_sixteen
    hV a (b ^ 2) ha (by simpa only [← pow_mul] using hb4) hinv
  let F := FixedPoints.subgroup (zpowers b) V
  have hFbound : Nat.card F ≤ 2 := by
    have hlt := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one b hb4 hbne
    rw [hfixedSquare] at hlt
    have hd := F.card_subgroup_dvd_card
    rw [hV] at hd
    have hn3 : Nat.card F ≠ 3 := by intro h3; norm_num [h3] at hd
    change Nat.card F < 4 at hlt
    omega
  have hfix (x : V) (hx5 : (Set.range (fun g => f g x)).ncard = 5)
      (hux : f u x = x) : x ∈ F := by
    let S := stabilizer M x
    have hScard : Nat.card S = 4 := by
      have hh := Nat.card_congr (orbitProdStabilizerEquivGroup M x)
      rw [Nat.card_prod, hM] at hh
      change (Set.range (fun g => f g x)).ncard * Nat.card S = 20 at hh
      rw [hx5] at hh
      omega
    have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 2) hScard
    let : IsCyclic S := (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ S hSp).1
    have huS : u ∈ S := hux
    have hSC : S ≤ C := by
      intro s hs
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨s, hs⟩ : S) (⟨u, huS⟩ : S))
    have heq : S = C := eq_of_le_of_card_ge hSC (by rw [hScard, hCcard])
    apply (MulAut.mem_fixed_zpowers_iff b x).mpr
    have hrS : (r : M) ∈ S := heq.symm ▸ r.property
    exact hrS
  have hvF := hfix v hv5 huv
  have hwF := hfix w hw5 huw
  have hFnontriv : Nontrivial F := ⟨⟨⟨v, hvF⟩, 1, fun hh => hv (congrArg Subtype.val hh)⟩⟩
  have hFcard : Nat.card F = 2 := by
    have hh := Finite.one_lt_card_iff_nontrivial.mpr hFnontriv
    omega
  obtain ⟨x, _, hx⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hFcard
  have hvx := hx ⟨v, hvF⟩ (fun hh => hv (congrArg Subtype.val hh))
  have hwx := hx ⟨w, hwF⟩ (fun hh => hw (congrArg Subtype.val hh))
  exact congrArg Subtype.val (hvx.trans hwx.symm)

end Theory.GroupAction
