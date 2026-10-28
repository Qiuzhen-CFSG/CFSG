module

public import Theory.GroupAction.IrreducibleTwoCoreKernel
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticAction
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# A five-element forces a two-core to fix a center

On an elementary abelian group of order sixteen, an automorphism of order
five is irreducible: orbit counting and Lagrange leave only the trivial and
whole invariant subgroups. A normal two-subgroup has nonzero fixed points,
so it fixes the entire group. This puts the two-core of any actor in the
kernel of this action.

If the acted-on group is a central quotient Q/Z(Q), kernel elements have
central displacement. That displacement is a homomorphism into the center,
so it kills the derived subgroup. When Q' = Z(Q), the actor's two-core
therefore fixes Z(Q) pointwise.

This source-independent argument supplies the intrinsic group-action step
in the PSU₃(4) inference in Aschbacher--Smith, proof of 15.3.40, printed
p.1138. The actual model and its order-five quotient action are separate
inputs; no automorphism-classification hypothesis is used.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupAction.FiveActorTwoCore

/-- A five-element in an action on E₁₆ makes the two-core act trivially. -/
theorem core_le_ker {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (hV : Nat.card V = 16)
    (f : A →* MulAut V) (a : A) (ha : orderOf (f a) = 5) :
    pCore 2 A ≤ f.ker := by
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let B := zpowers (f a)
  have hB : Nat.card B = 5 := (Nat.card_zpowers _).trans ha
  have hfixed := SmallNonabelianTwoGroup.order_five_actor_fixed_subgroup_eq_bot hV B hB
  apply irreducible_range_core_le_ker f
  intro D hD
  have hBR : B ≤ f.range := zpowers_le.mpr (⟨a, rfl⟩)
  have hforward (b : B) (v : V) (hv : v ∈ D) : b • v ∈ D :=
    hD ⟨b, hBR b.property⟩ v hv
  let : IsInvariant B V D := ⟨fun b v => ⟨hforward b v, fun hv => by
    simpa only [inv_smul_smul] using hforward b⁻¹ (b • v) hv⟩⟩
  exact invariant_eq_bot_or_top_of_five_actor hB hV hfixed D

/-- An automorphism trivial modulo the center fixes the derived subgroup pointwise. -/
theorem fixes_derived_of_quotient_center_eq_one
    {Q : Type*} [Group Q] (a : MulAut Q)
    (ha : quotientAut (center Q) a = 1) :
    ∀ x ∈ commutator Q, a x = x := by
  have hdisp (x : Q) : x⁻¹ * a x ∈ center Q := by
    apply QuotientGroup.eq.mp
    have hx := DFunLike.congr_fun ha (QuotientGroup.mk' (center Q) x)
    rw [quotientAut_apply_mk] at hx
    exact hx.symm
  let d : Q →* center Q := {
    toFun x := ⟨x⁻¹ * a x, hdisp x⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' x y := by
      apply Subtype.ext
      change (x * y)⁻¹ * a (x * y) = (x⁻¹ * a x) * (y⁻¹ * a y)
      rw [mul_inv_rev, map_mul]
      have hc := mem_center_iff.mp (hdisp x) y⁻¹
      calc
        y⁻¹ * x⁻¹ * (a x * a y) = (y⁻¹ * (x⁻¹ * a x)) * a y := by group
        _ = ((x⁻¹ * a x) * y⁻¹) * a y := by rw [hc]
        _ = _ := by group }
  intro x hx
  have hd : d x = 1 := Abelianization.commutator_subset_ker d hx
  have he := congrArg Subtype.val hd
  exact (inv_mul_eq_one.mp he).symm

/-- For a finite two-group whose center equals its derived subgroup,
an order-five automorphism remains of order five on the central quotient. -/
theorem order_five_on_central_quotient
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hderived : commutator Q = center Q) (a : MulAut Q) (ha : orderOf a = 5) :
    orderOf (quotientAut (center Q) a) = 5 := by
  have hdvd : orderOf (quotientAut (center Q) a) ∣ 5 :=
    ha ▸ orderOf_map_dvd (quotientAut (center Q)) a
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdvd with hone | hfive
  · exfalso
    have hquot : quotientAut (center Q) a = 1 := orderOf_eq_one_iff.mp hone
    have hpair : a ∈ (automorphismPair (center Q)).ker := by
      rw [MonoidHom.mem_ker, automorphismPair_apply]
      apply Prod.ext
      · ext z
        change a (z : Q) = (z : Q)
        exact fixes_derived_of_quotient_center_eq_one a hquot z (hderived.symm ▸ z.property)
      · exact hquot
    have hp := isPGroup_automorphism_pair_kernel (center Q) (hQ.to_subgroup (center Q))
    obtain ⟨n, hn⟩ := hp.exists_orderOf_dvd_pow ⟨a, hpair⟩
    have ho : orderOf (⟨a, hpair⟩ : (automorphismPair (center Q)).ker) = 5 :=
      (orderOf_injective (automorphismPair (center Q)).ker.subtype
        (automorphismPair (center Q)).ker.subtype_injective ⟨a, hpair⟩).symm.trans ha
    rw [ho] at hn
    exact (by decide : ¬ 5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hn)
  · exact hfive

/-- For Q with Q′ = Z(Q) and Q/Z(Q) ≅ E₁₆, a five-action forces center fixation. -/
theorem core_fixes_center {A Q : Type*} [Group A] [Finite A] [Group Q] [Finite Q]
    [IsElementaryAbelian 2 (Q ⧸ center Q)]
    (hQ : Nat.card (Q ⧸ center Q) = 16) (hderived : commutator Q = center Q)
    (f : A →* MulAut Q) (a : A)
    (ha : orderOf (quotientAut (center Q) (f a)) = 5) :
    ∀ b ∈ pCore 2 A, ∀ z ∈ center Q, f b z = z := by
  have hker := core_le_ker hQ ((quotientAut (center Q)).comp f) a ha
  intro b hb z hz
  exact fixes_derived_of_quotient_center_eq_one (f b) (hker hb) z (hderived.symm ▸ hz)

end Theory.GroupAction.FiveActorTwoCore
