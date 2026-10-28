module

public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace

/-!
# Order-thirteen inversion on a binary twelve-space

In a faithful binary representation of degree twelve, an element of order
thirteen has zero fixed space: its nonzero displacement is divisible by the
multiplicative order of two modulo thirteen, which is twelve. The commutator
rank inequality then bounds the fixed dimension of any inverting element by
six.

For an involution t in an actor A, equality C_V(A) = C_V(t) makes an actor
element a fix C_V(t). Its commutators with elements centralizing t also fix
that space. The P × Q lemma says such a commuting kernel is a two-group,
so a commutator of order three forces a strict drop in fixed dimension.
Combining the two observations gives dimension at most five.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10. These linear arguments apply to the actual ambient action;
constructing the PSL₃(3) group witnesses is a separate obligation.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Every order-thirteen element acts without fixed vectors in a faithful
binary twelve-dimensional representation. -/
theorem fixedSpace_order_thirteen_eq_bot_of_finrank_twelve (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12) (x : G) (hx : orderOf x = 13) :
    fixedSpace ρ (zpowers x) = ⊥ := by
  have hdiv : 12 ∣ fixedCodim ρ (zpowers x) := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_thirteen] using
      orderOf_two_dvd_fixedCodim_of_isPGroup ρ (by decide : Nat.Prime 13) (by decide)
        (zpowers x) (IsPGroup.of_card (p := 13) (n := 1) (by
          simpa only [Nat.card_zpowers, pow_one] using hx))
  have hn := fixedCodim_add_finrank ρ (zpowers x)
  rw [hd] at hn
  have hne : fixedCodim ρ (zpowers x) ≠ 0 := by
    intro hz
    have htop : fixedSpace ρ (zpowers x) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by omega)
    have he : ρ x = ρ 1 := by
      rw [map_one]
      ext v
      exact (mem_fixedSpace_zpowers_iff ρ x v).mp (by rw [htop]; trivial)
    have hx1 := hf he
    simp only [hx1, orderOf_one] at hx
    omega
  have hd12 : fixedCodim ρ (zpowers x) = 12 := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv
    omega
  apply Submodule.finrank_eq_zero.mp
  omega

/-- Inverting an order-thirteen element bounds fixed dimension by six. -/
theorem finrank_fixedSpace_le_six_of_inverts_thirteen (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12)
    (t x : G) (hx : orderOf x = 13) (hinv : t * x * t⁻¹ = x⁻¹) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) ≤ 6 := by
  have hx2 : orderOf (x ^ 2) = 13 := by
    rw [Nat.Coprime.orderOf_pow (show (orderOf x).Coprime 2 by rw [hx]; decide), hx]
  have hc : t * x * t⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by
    rw [hinv, pow_two, mul_inv_rev]
  have hcod : fixedCodim ρ (zpowers (t * x * t⁻¹ * x⁻¹)) = 12 := by
    have hn := fixedCodim_add_finrank ρ (zpowers (x ^ 2))
    rw [fixedSpace_order_thirteen_eq_bot_of_finrank_twelve ρ hf hd (x ^ 2) hx2, finrank_bot, add_zero, hd] at hn
    simpa only [hc, zpowers_inv] using hn
  have hi := fixedCodim_commutator_le_twice ρ t x
  have hn := fixedCodim_add_finrank ρ (zpowers t)
  omega

omit [FiniteDimensional (ZMod 2) V] in
private theorem preserves_fixed_of_commute (t c : G) (hcomm : Commute t c)
    {v : V} (hv : v ∈ fixedSpace ρ (zpowers t)) :
    ρ c v ∈ fixedSpace ρ (zpowers t) := by
  rw [mem_fixedSpace_zpowers_iff] at hv ⊢
  rw [← Module.End.mul_apply, ← map_mul, hcomm.eq, map_mul, Module.End.mul_apply, hv]

omit [FiniteDimensional (ZMod 2) V] in
private theorem commutator_fixes_of_fixes (t a c : G) (htc : Commute t c)
    (ha : ∀ v ∈ fixedSpace ρ (zpowers t), ρ a v = v) :
    zpowers (a * c * a⁻¹ * c⁻¹) ≤ subspaceKernel ρ (fixedSpace ρ (zpowers t)) ⊤ := by
  apply zpowers_le.mpr
  refine ⟨mem_top _, ?_⟩
  intro v hv
  have hai (w : V) (hw : w ∈ fixedSpace ρ (zpowers t)) : ρ a⁻¹ w = w := by
    have hh := congrArg (ρ a⁻¹) (ha w hw)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh.symm
  have hi := preserves_fixed_of_commute ρ t c⁻¹ htc.inv_right hv
  simp only [map_mul, Module.End.mul_apply]
  rw [hai _ hi]
  have hc : ρ c (ρ c⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hc, ha v hv]

/-- An odd commutator in the involution centralizer detects a strict loss
when intersecting its fixed space with the actor fixed space. -/
theorem finrank_fixedSpace_lt_of_three_commutator (hf : Function.Injective ρ)
    (A : Subgroup G) (t a c : G) (htA : t ∈ A) (haA : a ∈ A)
    (ht : orderOf t = 2) (hta : Commute t a) (htc : Commute t c)
    (hthree : orderOf (a * c * a⁻¹ * c⁻¹) = 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) <
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) := by
  have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv b
    exact hv ⟨b, (zpowers_le.mpr htA) b.property⟩
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne hle ?_
  intro heq
  have ha : ∀ v ∈ fixedSpace ρ (zpowers t), ρ a v = v := by
    intro v hv
    have hvA : v ∈ fixedSpace ρ A := heq ▸ hv
    exact hvA ⟨a, haA⟩
  let x := a * c * a⁻¹ * c⁻¹
  have htx : Commute t x := ((hta.mul_right htc).mul_right hta.inv_right).mul_right htc.inv_right
  have hP := isPGroup_of_commuting_fixes_fixedSpace ρ hf (zpowers t) (zpowers x)
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using ht))
    (by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      apply zpowers_le.mpr
      rw [mem_centralizer_iff]
      intro b hb
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
      exact (htx.zpow_right n).eq.symm)
    (commutator_fixes_of_fixes ρ t a c htc ha)
  have hxne : (⟨x, mem_zpowers x⟩ : zpowers x) ≠ 1 := by
    intro he
    have hxe : x = 1 := congrArg Subtype.val he
    change orderOf x = 3 at hthree
    simp only [hxe, orderOf_one] at hthree
    omega
  have hdiv := hP.dvd_orderOf hxne
  rw [Subgroup.orderOf_mk] at hdiv
  change 2 ∣ orderOf (a * c * a⁻¹ * c⁻¹) at hdiv
  rw [hthree] at hdiv
  norm_num at hdiv

/-- The graph eight-group witness gives the required strict degree-twelve bound. -/
theorem finrank_fixedSpace_le_five_of_thirteen_three_witness (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 12)
    (A : Subgroup G) (t x a c : G) (htA : t ∈ A) (haA : a ∈ A)
    (ht : orderOf t = 2) (hx : orderOf x = 13)
    (hinv : t * x * t⁻¹ = x⁻¹) (hta : Commute t a) (htc : Commute t c)
    (hthree : orderOf (a * c * a⁻¹ * c⁻¹) = 3) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 5 := by
  have hlt := finrank_fixedSpace_lt_of_three_commutator ρ hf A t a c htA haA ht hta htc hthree
  have hle := finrank_fixedSpace_le_six_of_inverts_thirteen ρ hf hd t x hx hinv
  omega

end Representation.BinaryOffender
