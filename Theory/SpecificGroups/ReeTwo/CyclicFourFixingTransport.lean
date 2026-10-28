module

public import Theory.SpecificGroups.ReeTwo.CyclicFourCentralExtensionTransport

/-!
# Changing the actor in a root-fixing cyclic-four extension

When the action fixes root 2, the actor commutes with that root. Since root 2
has fourth power one, multiplying the actor by root 2 preserves its fourth
power. The universal property identifies the inner-twisted action with the
original marked extension, including the nonsplit case.

Source: the verified Shinoda (1975), pp.81–83 core coordinates and the cyclic
carry construction in `CyclicFourCentralExtension`.
-/

@[expose] public section
namespace ReeTwo.CyclicFourCentralExtension

variable {β δ : MulAut Core} {hβ : β ^ 4 = 1} {hδ : δ ^ 4 = 1} {ε : Bool}

/-- Fixing root 2 also preserves the fourth-power parameter under actor change. -/
theorem shiftedActor_four_of_fix (hfix : β (Core.root 2) = Core.root 2) :
    (shiftedActor : Model β hβ ε) ^ 4 = embed (mark ε) := by
  have hc := actor_conj (beta := β) (hbeta := hβ) (epsilon := ε) (Core.root 2)
  rw [hfix] at hc
  have he : Commute (embed (Core.root 2) : Model β hβ ε) actor :=
    (mul_inv_eq_iff_eq_mul.mp hc).symm
  rw [shiftedActor, he.mul_pow, ← map_pow,
    show Core.root 2 ^ 4 = 1 from by decide +kernel, map_one, one_mul]
  exact actor_four

/-- Actor change for fixing actions, preserving the marked carry. -/
noncomputable def fixingShiftEquiv
    (hfix : β (Core.root 2) = Core.root 2)
    (h : ∀ q, δ q = Core.root 2 * β q * (Core.root 2)⁻¹) :
    Model δ hδ ε ≃* Model β hβ ε :=
  equiv embed shiftedActor
    (fun q => (shiftedActor_conj q).trans (congrArg embed (h q).symm))
    (shiftedActor_four_of_fix hfix) card shiftedActor_generate

@[simp] theorem fixingShiftEquiv_embed
    (hfix : β (Core.root 2) = Core.root 2)
    (h : ∀ q, δ q = Core.root 2 * β q * (Core.root 2)⁻¹) (q : Core) :
    fixingShiftEquiv (hβ := hβ) (hδ := hδ) (ε := ε) hfix h (embed q) = embed q :=
  equiv_embed ..

end ReeTwo.CyclicFourCentralExtension
