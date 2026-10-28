module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent.Quotient
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Natural.Matrix
public import Theory.SpecificGroups.SL2.NormalMonolith

/-!
# Sylow actions from the central involution in the nilpotent branch

This conditional reduction isolates one actual action equation: the central
involution of K/F*(K) ≃ SL₂(5) must invert the omega–Frattini quotient.
The SL₂ normal-monolith theorem then proves faithfulness and identifies the
kernel in K as F(K). A matrix quaternion subgroup lies in every Sylow
two-subgroup of the quotient and lifts into the actual Sylow action image.

For irreducibility, a proper nontrivial invariant subgroup has order p. Its
automorphism group is abelian, so the quaternion commutator fixes it. That
commutator acts by inversion, forcing the subgroup to be trivial.
The prime-order subgroup calculation follows the private argument in
`Actions.Natural.Matrix`, whose public matrix quaternion theorem is reused.

The inversion equation is still an explicit hypothesis here. Its derivation
from nontriviality, and the proof of nontriviality from the C-component and
common A.3.6 assertions, remain obligations of the nilpotent assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(4),
pp.43–45, and the actions in 1.3.3 and 1.3.8, pp.509, 513–514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent
section Abstract
variable {V : Type*} [Group V] [Finite V] {p : ℕ} [Fact p.Prime]

omit [Finite V] [Fact p.Prime] in
private theorem eq_one_of_inverse_eq (hp : Odd p) (hc : Nat.card V = p ^ 2)
    (x : V) (hx : x⁻¹ = x) : x = 1 := by
  have hx2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (fun y => y * x) hx.symm
      _ = 1 := inv_mul_cancel x
  have hd2 := orderOf_dvd_of_pow_eq_one hx2
  have hdp : orderOf x ∣ p ^ 2 := hc ▸ orderOf_dvd_natCard x
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_left.mpr hp).pow_right 2) hd2 hdp)

omit [Finite V] in
private theorem inversion_ne_one (hp : Odd p) (hc : Nat.card V = p ^ 2)
    (a : MulAut V) (ha : ∀ x, a x = x⁻¹) : a ≠ 1 := by
  intro heq
  have hV : Subsingleton V := ⟨fun x y => by
    have hfix (z : V) : z = 1 := eq_one_of_inverse_eq hp hc z (by
      simpa only [heq, MulAut.one_apply] using (ha z).symm)
    rw [hfix x, hfix y]⟩
  let := hV
  have hcard : Nat.card V = 1 := Nat.card_unique
  have hlt : 1 < p ^ 2 := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by decide)
  omega

private theorem quaternion_irreducible (hp : Odd p) (hc : Nat.card V = p ^ 2)
    (ρ : QuaternionGroup 2 →* MulAut V)
    (hz : ∀ x : V, ρ (.a 2) x = x⁻¹)
    (A : Subgroup V) (hA : ∀ g x, x ∈ A → ρ g x ∈ A) : A = ⊥ ∨ A = ⊤ := by
  have hd : Nat.card A ∣ p ^ 2 := hc ▸ A.card_subgroup_dvd_card
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  interval_cases k
  · exact Or.inl (A.eq_bot_of_card_eq (by simpa using he))
  · have hcard : Nat.card A = p := by simpa using he
    let : IsCyclic A := isCyclic_of_prime_card hcard
    let ψ : QuaternionGroup 2 →* MulAut A :=
      { toFun := fun g =>
          { toFun := fun x => ⟨ρ g x, hA g x x.property⟩
            invFun := fun x => ⟨ρ g⁻¹ x, hA g⁻¹ x x.property⟩
            left_inv := fun x => Subtype.ext (by simp)
            right_inv := fun x => Subtype.ext (by simp)
            map_mul' := fun x y => Subtype.ext (map_mul (ρ g) (x : V) (y : V)) }
        map_one' := by ext x; change ρ 1 (x : V) = (x : V); simp
        map_mul' := by
          intro g h; ext x
          change ρ (g * h) (x : V) = ρ g (ρ h (x : V))
          rw [map_mul]; rfl }
    have hcomm (g h : QuaternionGroup 2) : ψ g * ψ h = ψ h * ψ g := by
      apply (IsCyclic.mulAutMulEquiv A).injective
      simp only [map_mul]
      exact mul_comm _ _
    have hzψ : ψ (.a 2) = 1 := by
      rw [show (QuaternionGroup.a 2 : QuaternionGroup 2) =
        .a 1 * .xa 0 * (.a 1)⁻¹ * (.xa 0)⁻¹ by decide]
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hinv (x : A) : x⁻¹ = x := by
      apply Subtype.ext
      have heq := congrArg (fun f : MulAut A => (f x : V)) hzψ
      change ρ (.a 2) (x : V) = (x : V) at heq
      exact (hz x).symm.trans heq
    have htrivial (x : A) : x = 1 := by
      have hs : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := pow_two x
             _ = x⁻¹ * x := congrArg (fun y => y * x) (hinv x).symm
             _ = 1 := inv_mul_cancel x
      have hd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hs
      have hdp : orderOf x ∣ p := hcard ▸ orderOf_dvd_natCard x
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.coprime_two_left.mpr hp) hd2 hdp)
    exact Or.inl (by apply bot_unique; intro x hx; exact congrArg Subtype.val (htrivial ⟨x, hx⟩))
  · exact Or.inr (A.eq_top_of_card_eq (he.trans hc.symm))

end Abstract

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

/-- Central inversion detects the entire quotient-action kernel via the SL₂ normal monolith. -/
theorem quotientAction_injective_of_inversion
    (h : A36Nilpotent K) (hd : p ∣ Nat.card (fittingSubgroup K))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5)
    (e : (K ⧸ generalizedFitting K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hz : ∀ x, quotientAction h hd (e.symm (-1)) x = x⁻¹) :
    Function.Injective (quotientAction h hd) := by
  let σ := (quotientAction h hd).comp e.symm.toMonoidHom
  have hp3 := (RadicalStructure.radical_core (Or.inr h) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have htwo : (2 : F) ≠ 0 := by
    let : Fintype F := Fintype.ofFinite F
    let r : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    intro he
    have : r (2 : ZMod 5) = r 0 := by
      calc
        r (2 : ZMod 5) = (2 : F) := map_ofNat r 2
        _ = 0 := he
        _ = r 0 := (map_zero r).symm
    exact (by decide : (2 : ZMod 5) ≠ 0) (r.injective this)
  have hfaith : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply Matrix.SpecialLinearGroup.eq_bot_of_neg_one_not_mem htwo
    intro hzker
    exact inversion_ne_one ho (frattini_shape h hd).2 (σ (-1)) hz
      (MonoidHom.mem_ker.mp hzker)
  intro a b hab
  apply e.injective
  apply hfaith
  change quotientAction h hd (e.symm (e a)) = quotientAction h hd (e.symm (e b))
  simpa only [e.symm_apply_apply] using hab

/-- Once the central-involution equation is proved, the kernel is exactly the Fitting subgroup. -/
theorem action_ker_eq_fitting_of_inversion
    (h : A36Nilpotent K) (hd : p ∣ Nat.card (fittingSubgroup K))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5)
    (e : (K ⧸ generalizedFitting K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hz : ∀ x, quotientAction h hd (e.symm (-1)) x = x⁻¹) :
    (omegaFrattiniAction p K).ker = fittingSubgroup K := by
  apply le_antisymm _ (fitting_le_action_ker h hd)
  intro g hg
  rw [← h.1]
  apply (QuotientGroup.eq_one_iff _).mp
  apply quotientAction_injective_of_inversion h hd hF e hz
  rw [map_one]
  change omegaFrattiniAction p K g = 1
  exact MonoidHom.mem_ker.mp hg

/-- The actual Sylow-two action conclusions, conditional on the precise remaining
central-involution equation. This is not the unconditional A.3.6 action theorem. -/
theorem sylow_actions_of_inversion
    (h : A36Nilpotent K) (hd : p ∣ Nat.card (fittingSubgroup K))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5)
    (e : (K ⧸ generalizedFitting K) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hz : ∀ x, quotientAction h hd (e.symm (-1)) x = x⁻¹)
    (S : Sylow 2 K) :
    (∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
      (∀ (s : S) x, x ∈ A → omegaFrattiniAction p K s x ∈ A) → A = ⊥ ∨ A = ⊤) ∧
    ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype).range,
      Function.Injective f := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (generalizedFitting K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S' := S.mapSurjective hq
  obtain ⟨f, hf, hfz⟩ := Natural.sylow_quaternion (p := 5) (by decide) hF S'
  let σ := (quotientAction h hd).comp e.symm.toMonoidHom
  have hσ : Function.Injective σ :=
    (quotientAction_injective_of_inversion h hd hF e hz).comp e.symm.injective
  have hcompat (g : K) : σ (q g) = omegaFrattiniAction p K g := by
    change quotientAction h hd (e.symm (e (QuotientGroup.mk' _ g))) = _
    rw [e.symm_apply_apply, quotientAction_apply_mk]
  let τ := σ.comp ((S' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype.comp f)
  have hτ : Function.Injective τ :=
    hσ.comp ((S' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype_injective.comp hf)
  have hτz (x : omegaCore p K ⧸ frattini (omegaCore p K)) : τ (.a 2) x = x⁻¹ := by
    change σ (f (.a 2)) x = x⁻¹
    rw [hfz]
    exact hz x
  have hp3 := (RadicalStructure.radical_core (Or.inr h) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  constructor
  · intro A hA
    apply quaternion_irreducible ho (frattini_shape h hd).2 τ hτz A
    intro g x hx
    obtain ⟨s, hs, hsg⟩ := (f g).property
    change σ (f g) x ∈ A
    rw [← hsg, hcompat]
    exact hA ⟨s, hs⟩ x hx
  · let ρ := (omegaFrattiniAction p K).comp (S : Subgroup K).subtype
    have hm (g : QuaternionGroup 2) : τ g ∈ ρ.range := by
      obtain ⟨s, hs, hsg⟩ := (f g).property
      refine ⟨⟨s, hs⟩, ?_⟩
      change omegaFrattiniAction p K s = σ (f g)
      rw [← hsg, hcompat]
    exact ⟨τ.codRestrict ρ.range hm, fun x y hxy => hτ (congrArg Subtype.val hxy)⟩

end CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent
