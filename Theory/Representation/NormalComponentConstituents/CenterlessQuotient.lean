module
public import Theory.Representation.NormalComponentConstituents

/-!
# Centerless quotients detected by a constituent

The center of a normal subgroup maps into the center of each quotient. If a
nonzero constituent factors through a centerless quotient, the embedded
center fixes that constituent. Ambient faithful irreducibility then makes
the center trivial. No faithfulness of the constituent is assumed.

Source: the constituent-kernel step in Aschbacher--Smith G.10.15,
printed pp.362--363.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
namespace Representation.BinaryOffender
/-- The center of a normal subgroup vanishes when a nonzero constituent
factors through a centerless quotient, in a faithful irreducible ambient action. -/
theorem center_eq_bot_of_constituent_quotient
    {D Q V : Type*} [Group D] [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (hi : IsIrreducible ρ) (H : Subgroup D) [H.Normal]
    (I : Submodule (ZMod 2) V) (hI : H ≤ subspaceStabilizer ρ I) (hne : I ≠ ⊥)
    (p : H →* Q) (hp : Function.Surjective p) (hc : center Q = ⊥)
    (hkill : ∀ a, p a = 1 → (invariantSubspace ρ H I hI).toRepresentation a = 1) :
    center H = ⊥ := by
  let Z := (center H).map H.subtype
  let : Z.Normal := inferInstanceAs ((center H).map H.subtype).Normal
  have hfix : I ≤ fixedSpace ρ Z := by
    intro u hu z
    obtain ⟨a,ha,he⟩ := z.property
    have ha1 : p a = 1 := by
      apply mem_bot.mp
      rw [←hc]
      apply mem_center_iff.mpr
      intro b
      obtain ⟨c,rfl⟩ := hp b
      exact (map_mul p c a).symm.trans
        ((congrArg p (mem_center_iff.mp ha c)).trans (map_mul p a c))
    have hh := congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩:V)) (hkill a ha1)
    change ρ (z:D) u = u
    change ρ (a:D) u = u at hh
    change (a:D) = (z:D) at he
    rwa [he] at hh
  have hZ : Z = ⊥ := by
    by_contra hz
    have hzero := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi Z hz
    exact hne (bot_unique (hzero ▸ hfix))
  exact (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hZ
end Representation.BinaryOffender

