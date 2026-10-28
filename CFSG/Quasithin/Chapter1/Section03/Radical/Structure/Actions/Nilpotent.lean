module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent.Inversion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions.Nilpotent

/-!
# The nilpotent A.3.6 omega action

The actual omega–Frattini quotient has order p², and its conjugation action
factors through K/F*(K) ≃ SL₂(5). Once the central involution is proved to act
by inversion, the action kernel is exactly F(K), every Sylow two-subgroup acts
irreducibly, and its image contains an injective quaternion group of order eight.

The source leaf `CenterFrattiniSource.OmegaActions.Nilpotent` proves the
remaining action theorem.  The C-component wrapper below installs the
perfectness instance supplied by a C-component and keeps the SQTK,
trivial-two-core and common A.3.6 hypotheses at the source-facing boundary.
No center–Frattini equality or exponent-one assumption is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6(4),
pp.43–45, and 1.3.3/1.3.8, pp.509, 513–514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent

universe u

/-- The actual Sylow-two action for a nilpotent A.3.6 C-component.

The action is conjugation on the actual omega--Frattini quotient, and the
quaternion homomorphism lands in the actual restricted action range.
-/
theorem nilpotent_sylow_actions
    {𝒦 : GroupClass.{u}} {E : Type u} [Group E] [Finite E]
    (_hE : IsSQTK 𝒦 E) (_hO : pCore 2 E = ⊥)
    {C : Subgroup E} (hC : C.IsCComponent)
    (hnil : A36Nilpotent C) (_hcommon : A36Common C)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup C)) (S : Sylow 2 C) :
    (∀ A : Subgroup (omegaCore p C ⧸ frattini (omegaCore p C)),
      (∀ (s : S) x, x ∈ A → omegaFrattiniAction p C s x ∈ A) →
        A = ⊥ ∨ A = ⊤) ∧
    ∃ f : QuaternionGroup 2 →*
        ((omegaFrattiniAction p C).comp (S : Subgroup C).subtype).range,
      Function.Injective f := by
  let : Group.IsPerfect C := hC.perfect
  exact CenterFrattiniSource.nilpotent_sylow_actions hnil hp hd S

end CFSG.Quasithin.Chapter1.RadicalActions.Nilpotent
