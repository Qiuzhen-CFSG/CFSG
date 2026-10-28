module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Cubic
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.PrimePowerDecomposition
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Faithful three-subgroup actions on the residual two-core

In the equality row Kc = K, cubic generation puts every element of order
three of Mc in K. The genuine Xi-to-characteristic-two bridge then shows
that C_Mc(O₂(K)) has order prime to three: a hypothetical cubic element
there lies in C_K(O₂(K)) ≤ O₂(K). Thus the actual conjugation action on
O₂(K) preserves three-power orders. The Burnside basis kernel theorem
passes this detection to O₂(K)/Φ(O₂(K)), and every three-subgroup of Mc
acts faithfully on that quotient.

The final two theorems apply this reduction to the literal partner
residual and index. They retain the order-nine action exclusion explicitly;
no bound on the whole two-core or its Frattini quotient is inferred from
the chosen four-dimensional module. The ambient order-nine exclusion and
Held exclusion remain with `qt-e-152-residual-geometry`. The parent
`qt-e-152-plane-geometry` supplies the earlier premises in `ResidualInput`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
15.2.12(4), printed p.1111, the equality-row kernel calculation.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Section01
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- The residual inherits characteristic two from its actual Sylow overgroup. -/
theorem ResidualInput.residual_characteristic_two
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B) :
    centralizer (pCore 2 (residual H) : Set (residual H)) ≤ pCore 2 (residual H) := by
  apply mem_He_iff.mp
  apply d.mem_Xi.mem_He
  · intro A hA N hN hNA hn
    exact lemma_1_1_3_1 hA hN hNA hn
  · exact lemma_1_1_4_6 T (h.ambient.evenCharacteristic T)

/-- The partner centralizer of the residual two-core has order prime to three. -/
theorem ResidualInput.residual_core_centralizer_three_free
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    Nat.Coprime 3 (Nat.card ((centralizer ((residual H).pCoreIn 2 : Set G)).subgroupOf Mc)) := by
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card'
    (G := (centralizer ((residual H).pCoreIn 2 : Set G)).subgroupOf Mc) 3 hd
  have hp : (x : Mc) ^ 3 = 1 := by
    have hh := pow_orderOf_eq_one x
    rw [hx] at hh
    exact congrArg Subtype.val hh
  have hxK := d.cubic_mem_residual_of_eq he (x : Mc) hp
  let y : residual H := ⟨((x : Mc) : G), hxK⟩
  have hyC : y ∈ centralizer (pCore 2 (residual H) : Set (residual H)) := by
    intro z hz
    apply Subtype.ext
    exact (show ((x : Mc) : G) ∈ centralizer ((residual H).pCoreIn 2 : Set G) from x.property)
      (z : G) ⟨z,hz,rfl⟩
  have hyQ := d.residual_characteristic_two hyC
  let z : pCore 2 (residual H) := ⟨y,hyQ⟩
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := residual H)) z
  have ho : orderOf z = 3 := by
    dsimp only [z,y]
    simpa only [Subgroup.orderOf_mk,Subgroup.orderOf_coe] using hx
  have hd2 := orderOf_dvd_of_pow_eq_one hn
  rw [ho] at hd2
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd2)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Chapter1 Section01
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}

/-- Conjugation by the partner restricted to the residual two-core. -/
@[expose] noncomputable def partnerCoreAction (H Mc : Subgroup G)
    (he : partnerSpan H Mc = residual H) : Mc →* MulAut (pCore 2 (residual H)) :=
  (MulAut.characteristic (pCore 2 (residual H))).comp
    ((residual H).normalizerMonoidHom.comp
      (inclusion (partner_normalizes_of_eq H Mc he)))

omit [Finite G] in
/-- The action kernel is the literal ambient core centralizer inside Mc. -/
theorem partnerCoreAction_ker (H Mc : Subgroup G)
    (he : partnerSpan H Mc = residual H) :
    (partnerCoreAction H Mc he).ker =
      (centralizer ((residual H).pCoreIn 2 : Set G)).subgroupOf Mc := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ centralizer ((residual H).pCoreIn 2 : Set G)
    rintro _ ⟨y,hy,rfl⟩
    have hh := congrArg (fun a : MulAut (pCore 2 (residual H)) =>
      (((a ⟨y,hy⟩) : residual H) : G))
      (show partnerCoreAction H Mc he x = 1 from hx)
    change (x : G) * (y : G) * (x : G)⁻¹ = (y : G) at hh
    exact ((mul_inv_eq_iff_eq_mul).mp hh).symm
  · intro hx
    change partnerCoreAction H Mc he x = 1
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change (x : G) * ((y : residual H) : G) * (x : G)⁻¹ = ((y : residual H) : G)
    have hh := (show (x : G) ∈ centralizer ((residual H).pCoreIn 2 : Set G) from hx)
      ((y : residual H) : G) ⟨(y : residual H),y.property,rfl⟩
    rw [← hh, mul_inv_cancel_right]

/-- The actual core action has a kernel of order prime to three. -/
theorem ResidualInput.partnerCoreAction_kernel_three_free
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) :
    Nat.Coprime 3 (Nat.card (partnerCoreAction H Mc he).ker) := by
  rw [partnerCoreAction_ker]
  exact d.residual_core_centralizer_three_free he

/-- The core action preserves the order of every three-element. -/
theorem ResidualInput.partnerCoreAction_preserves_three_order
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) (x : Mc) {n : ℕ}
    (hx : x ^ (3 ^ n) = 1) : orderOf (partnerCoreAction H Mc he x) = orderOf x :=
  (partnerCoreAction H Mc he).orderOf_eq_of_prime_power_of_coprime_ker
    (d.partnerCoreAction_kernel_three_free he) x ⟨n,hx⟩

/-- The action on the Frattini quotient of the residual's own two-core. -/
@[expose] noncomputable def partnerCoreFrattiniAction (H Mc : Subgroup G)
    (he : partnerSpan H Mc = residual H) :
    Mc →* MulAut ((pCore 2 (residual H)) ⧸ frattini (pCore 2 (residual H))) :=
  (quotientAut (frattini (pCore 2 (residual H)))).comp (partnerCoreAction H Mc he)

/-- Passing to the Frattini quotient still preserves three-power orders. -/
theorem ResidualInput.partnerCoreFrattiniAction_preserves_three_order
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) (x : Mc) {n : ℕ}
    (hx : x ^ (3 ^ n) = 1) :
    orderOf (partnerCoreFrattiniAction H Mc he x) = orderOf x := by
  have ho := d.partnerCoreAction_preserves_three_order he x hx
  have hc : Nat.Coprime 2 (orderOf (partnerCoreAction H Mc he x)) := by
    rw [ho]
    exact ((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hx)
  exact ((quotientAut (frattini (pCore 2 (residual H)))).orderOf_map_eq_of_coprime_of_isPGroup_ker
    (isPGroup_quotientAut_frattini_kernel (pCore_isPGroup (p := 2) (G := residual H)))
    (partnerCoreAction H Mc he x) hc).trans ho

/-- Every three-subgroup acts faithfully on the core Frattini quotient. -/
theorem ResidualInput.partnerCoreFrattiniAction_injective_on_three_subgroup
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H) (P : Subgroup Mc) (hP : IsPGroup 3 P) :
    Function.Injective ((partnerCoreFrattiniAction H Mc he).comp P.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨n,hn⟩ := hP x
  have ho := d.partnerCoreFrattiniAction_preserves_three_order he (x : Mc)
    (congrArg Subtype.val hn)
  have hi : partnerCoreFrattiniAction H Mc he (x : Mc) = 1 := hx
  rw [hi,orderOf_one] at ho
  exact Subtype.ext (orderOf_eq_one_iff.mp ho.symm)

/-- Exclusion of order nine in the actual core-Frattini action suffices
for the literal residual identity; the ambient exclusion remains local work. -/
theorem ResidualInput.residual_equality_of_core_frattini_action
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (ha : ∀ he : partnerSpan H Mc = residual H,
      ∀ x : Mc, orderOf (partnerCoreFrattiniAction H Mc he x) ≠ 9) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  apply d.residual_equality_of_no_order_nine
  intro he x hx
  apply ha he x
  exact (d.partnerCoreFrattiniAction_preserves_three_order he x (n := 2)
    (by rw [show 3 ^ 2 = 9 by decide, ← hx, pow_orderOf_eq_one])).trans hx

/-- The same actual action exclusion supplies the required index bound. -/
theorem ResidualInput.index_coprime_of_core_frattini_action
    {h : ChosenSmallSource T M Mc V} (d : ResidualInput h H B)
    (ha : ∀ he : partnerSpan H Mc = residual H,
      ∀ x : Mc, orderOf (partnerCoreFrattiniAction H Mc he x) ≠ 9) :
    Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index := by
  apply d.index_coprime_of_no_order_nine
  intro he x hx
  apply ha he x
  exact (d.partnerCoreFrattiniAction_preserves_three_order he x (n := 2)
    (by rw [show 3 ^ 2 = 9 by decide, ← hx, pow_orderOf_eq_one])).trans hx

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
