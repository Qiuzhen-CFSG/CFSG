module

public import Theory.SpecificGroups.SL2.DegreeTwoActions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent.Inversion
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent.Nontrivial

/-!
# The nilpotent A.3.6 omega action

The actual conjugation action on Ω₁(Oₚ(B))/Φ(Ω₁(Oₚ(B))) descends through
B/F*(B), whose matrix model is SL₂(5). Perfectness makes that action
nontrivial, by `RadicalActions.Nilpotent.Nontrivial`; the new degree-two
matrix theorem therefore makes the central involution act by inversion.
The existing quaternion argument supplies irreducibility on every Sylow
two-subgroup and an injective Q₈ in its actual action image.

These conclusions require no extra representation witness, central-involution
equation, center–Frattini equality or exponent-p condition on the full core.
We keep the stronger perfect-group hypotheses actually used by the proof.
The C-component application supplies perfectness from its definition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of A.3.6,
printed pp.44–45, and the radical actions in 1.3.3 and 1.3.8, pp.509, 513–514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Matrix
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalActions
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private noncomputable def primeFieldSL2Equiv {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) : SL(2,F) ≃* SL(2,ZMod 5) := by
  let : Fintype F := Fintype.ofFinite F
  let r := ZMod.ringEquivOfPrime F (by decide : Nat.Prime 5)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact {
    toFun := SpecialLinearGroup.map r.symm.toRingHom
    invFun := SpecialLinearGroup.map r.toRingHom
    left_inv := by intro g; ext i j; exact r.apply_symm_apply _
    right_inv := by intro g; ext i j; exact r.symm_apply_apply _
    map_mul' := by intro g h; exact map_mul _ g h }

/-- The quotient action is nontrivial, so its central involution inverts the
actual omega–Frattini quotient. No center–Frattini equality is assumed. -/
theorem nilpotent_exists_inverting_quotient
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (h : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K)) :
    ∃ e : (K ⧸ generalizedFitting K) ≃* SL(2,ZMod 5),
      ∀ x, Nilpotent.quotientAction h hd (e.symm (-1)) x = x⁻¹ := by
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := h.2.2.1
  let e := eF.trans (primeFieldSL2Equiv hF)
  let ρ := (Nilpotent.quotientAction h hd).comp e.symm.toMonoidHom
  have hρ : ρ ≠ 1 := by
    intro he
    apply Nilpotent.omegaFrattiniAction_ne_one_of_perfect h hp hd
    ext g : 1
    have hg := DFunLike.congr_fun he (e (QuotientGroup.mk' (generalizedFitting K) g))
    simpa only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, Nilpotent.quotientAction_apply_mk, MonoidHom.one_apply] using hg
  let := (Nilpotent.frattini_shape h hd).1
  exact ⟨e, SpecialLinearGroup.DegreeTwo.action_neg_one_of_nontrivial hp
    (Nilpotent.frattini_shape h hd).2 ρ hρ⟩

/-- Irreducible Sylow-two action and a quaternion subgroup in its actual image
follow from the displayed nilpotent A.3.6 alternative and perfectness. -/
theorem nilpotent_sylow_actions
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (h : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K)) (S : Sylow 2 K) :
    (∀ A : Subgroup (omegaCore p K ⧸ frattini (omegaCore p K)),
      (∀ (s : S) x, x ∈ A → omegaFrattiniAction p K s x ∈ A) → A = ⊥ ∨ A = ⊤) ∧
    ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p K).comp (S : Subgroup K).subtype).range,
      Function.Injective f := by
  obtain ⟨e, hz⟩ := nilpotent_exists_inverting_quotient h hp hd
  exact Nilpotent.sylow_actions_of_inversion h hd (by simp : Nat.card (ZMod 5) = 5) e hz S

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
