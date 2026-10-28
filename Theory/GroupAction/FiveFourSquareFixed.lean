module

public import Theory.GroupAction.FiveInvertingInvolutionFixed
public import Theory.GroupAction.FourthPowerHyperplane
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolutionCentralizer
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Square-fixed points in a faithful five-four action

In C₅⋊C₄ with faithful complement action, a point fixed by the square
of an order-four element but moved by that element cannot have orbit
size five. A five-point orbit has stabilizer of order four. This
stabilizer is abelian and hence centralizes the square; the involution
centralizer also has order four and contains the original element.

For a faithful action on elementary sixteen the order-four element and
its square fix two and four elements respectively. These counts combine
with the binary hyperplane displacement calculation to give a line
whose nonidentity element has orbit size different from five.

Source: the five-four quotient action in D. Parrott,
*A characterization of the Tits' simple group* (1972), pp.673–674, 677.
-/

namespace Theory.GroupAction
open Subgroup MulAction
open scoped IsMulCommutative

private abbrev C5 := Multiplicative (ZMod 5)
private abbrev C4 := Multiplicative (ZMod 4)

/-- A square-fixed point moved by an order-four element does not lie in
a five-point orbit of the faithful five-four group. -/
public theorem five_four_orbit_card_ne_five_of_square_fixed
    {X : Type*} [Finite X]
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    [MulAction (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) X]
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4)
    (x : X) (hsquare : g ^ 2 • x = x) (hmove : g • x ≠ x) :
    (orbit (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) x).ncard ≠ 5 := by
  let M := Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)
  let : Finite M := Finite.of_equiv (C5 × C4) SemidirectProduct.equivProd.symm
  let S := stabilizer M x
  have hM : Nat.card M = 20 := by
    rw [SemidirectProduct.card]
    change Nat.card (ZMod 5) * Nat.card (ZMod 4) = 20
    simp
  intro hfive
  have hcount : (orbit M x).ncard * Nat.card S = 20 := by
    change Nat.card (orbit M x) * Nat.card S = 20
    rw [← hM, ← Nat.card_prod]
    exact Nat.card_congr (orbitProdStabilizerEquivGroup M x)
  have hS : Nat.card S = 4 := by rw [hfive] at hcount; omega
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsMulCommutative S :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hS)
  have hg2 : orderOf (g ^ 2) = 2 := by rw [orderOf_pow, hg]; decide
  have hC := (faithful_five_four_involution_centralizer φ hφ (g ^ 2) hg2).2
  have hSC : S ≤ centralizer ({g ^ 2} : Set M) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (mul_comm (⟨s, hs⟩ : S) ⟨g ^ 2, hsquare⟩)
  have heq : S = centralizer ({g ^ 2} : Set M) :=
    eq_of_le_of_card_ge hSC (by rw [hS, hC])
  apply hmove
  change g ∈ S
  rw [heq]
  exact mem_centralizer_singleton_iff.mpr (Commute.self_pow g 2).eq

/-- Every order-four element in a faithful five-four action on elementary
sixteen fixes two points, and its square fixes four. -/
public theorem five_four_sixteen_order_four_fixed_cards
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →* MulAut W) (hf : Function.Injective f)
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4) :
    Nat.card (FixedPoints.subgroup (zpowers (f g)) W) = 2 ∧
      Nat.card (FixedPoints.subgroup (zpowers ((f g) ^ 2)) W) = 4 := by
  let : Finite (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) :=
    Finite.of_equiv (C5 × C4) SemidirectProduct.equivProd.symm
  let d : C5 := Multiplicative.ofAdd (1 : ZMod 5)
  let a : MulAut W := f (SemidirectProduct.inl d)
  let b := f g
  have hd : orderOf d = 5 := by simp [d, orderOf_ofAdd_eq_addOrderOf]
  have ha : orderOf a = 5 := by
    rw [orderOf_injective f hf,
      orderOf_injective SemidirectProduct.inl SemidirectProduct.inl_injective, hd]
  have hb : orderOf b = 4 := (orderOf_injective f hf g).trans hg
  have hb4 : b ^ 4 = 1 := hb ▸ pow_orderOf_eq_one b
  have hbne : b ≠ 1 := by intro heq; simp [heq] at hb
  have hg2 : orderOf (g ^ 2) = 2 := by rw [orderOf_pow, hg]; decide
  have hinverts : b ^ 2 * a * (b ^ 2)⁻¹ = a⁻¹ := by
    have hh := congrArg f
      (faithful_five_four_involution_inverts_left φ hφ (g ^ 2) hg2 d)
    simpa only [map_mul, map_pow, map_inv] using hh
  have hb22 : (b ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hb4
  have hF2 := card_fixed_of_involution_inverting_five_on_sixteen
    hW a (b ^ 2) ha hb22 hinverts
  refine ⟨?_, hF2⟩
  have hlt := MulAut.fixed_card_lt_square_fixed_card_of_fourth_power_eq_one b hb4 hbne
  rw [hF2] at hlt
  have hp : IsPGroup 2 (zpowers b) := IsPGroup.of_card (n := 2)
    (by rw [Nat.card_zpowers, hb]; decide)
  have hmod := hp.card_modEq_card_fixedPoints W
  change Nat.ModEq 2 (Nat.card W) (Nat.card (FixedPoints.subgroup (zpowers b) W)) at hmod
  have hpos : 0 < Nat.card (FixedPoints.subgroup (zpowers b) W) := Nat.card_pos
  rw [hW] at hmod
  unfold Nat.ModEq at hmod
  change Nat.card (FixedPoints.subgroup (zpowers b) W) = 2
  omega

/-- The square displacement of a noninvariant binary hyperplane is a line
whose nonidentity element does not have orbit size five. -/
public theorem five_four_square_displacement_line
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →* MulAut W) (hf : Function.Injective f)
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4)
    (U : Subgroup W) (hU : Nat.card U = 8)
    (hU2 : ∀ u ∈ U, f g (f g u) ∈ U)
    (hUnot : ∃ u ∈ U, f g u ∉ U) :
    ∃ s : W →* W, (∀ w, s w = f g (f g w) * w) ∧
      Nat.card (U.map s) = 2 ∧
      ∀ w ∈ U.map s, w ≠ 1 → (Set.range (fun k => f k w)).ncard ≠ 5 := by
  let a := f g
  have hg4 : g ^ 4 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have ha4 : a ^ 4 = 1 := by
    change (f g) ^ 4 = 1
    rw [← map_pow, hg4, map_one]
  obtain ⟨hF, hF2⟩ := five_four_sixteen_order_four_fixed_cards hW φ hφ f hf g hg
  obtain ⟨s, hs, hline, hmove⟩ :=
    MulAut.square_displacement_of_noninvariant_hyperplane a ha4 hW hF hF2 U hU hU2 hUnot
  refine ⟨s, hs, hline, ?_⟩
  intro w hw hwne
  let : MulDistribMulAction (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) W := MulDistribMulAction.compHom W f
  apply five_four_orbit_card_ne_five_of_square_fixed φ hφ g hg w ?_ (hmove w hw hwne)
  obtain ⟨u, _, rfl⟩ := hw
  change f (g ^ 2) (s u) = s u
  rw [map_pow, hs]
  change a (a (a (a u) * u)) = a (a u) * u
  have hfour : a (a (a (a u))) = u := congrArg (fun b : MulAut W => b u) ha4
  simp only [map_mul, hfour]
  exact mul_comm _ _

end Theory.GroupAction
