module

public import Theory.Representation.SL2FourNaturalBorelFixedLifting.Gaschutz
public import Theory.Representation.FirstCohomology

/-!
# Borel detection for natural crossed homomorphisms

A natural SL₂(4) cocycle that vanishes on a subgroup mapping onto the
Borel and containing a Sylow two-subgroup is zero. Apply Gaschütz fixed
lifting to the canonical action on crossed homomorphisms. Its principal
submodule is the original natural module, and its fixed space is zero.
This applies directly to the commutator cocycle of an original group
element, without assuming that the containing group is elementary abelian.

Source: Aschbacher–Smith,14.7.74,the second Gaschütz step,printed p.1077.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix.SpecialLinearGroup
namespace Representation.SL2FourNaturalBorelFixedLifting
open OneCohomology
variable {A : Type*} [Group A] [Finite A]

/-- The natural commutator cocycle is detected on the original Borel preimage. -/
theorem cocycle_eq_zero_of_borel
    (q : A →* SL) (hq : Function.Surjective q)
    (B : Subgroup A) (S : Sylow 2 A) (hSB : (S : Subgroup A) ≤ B)
    (hmark : B.map q = rankOneBorel F)
    (f : cocycles (SL2FourNatural.naturalRepresentation.comp q))
    (hf : ∀ b ∈ B, f.val b = 0) : f = 0 := by
  let ρ := SL2FourNatural.naturalRepresentation.comp q
  have hfixed : fixed ρ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hb : v ∈ fixedSpace SL2FourNatural.naturalRepresentation (rankOneBorel F) := by
      rintro ⟨b,hb⟩
      obtain ⟨a,ha,rfl⟩ := hmark.symm ▸ hb
      exact hv a
    simpa only [natural_borel_fixedSpace_eq_bot, Submodule.mem_bot] using hb
  let i : IntertwiningMap ρ (universalAction ρ) :=
    (principal ρ).intertwiningMap_of_isIntertwiningMap _ _
      (fun a v => (universalAction_principal ρ a v).symm)
  have hdisp : ∀ a y, universalAction ρ a y - y ∈ i.toLinearMap.range := by
    intro a y
    refine ⟨y.val a, ?_⟩
    change principal ρ (y.val a) = y + principal ρ (y.val a) - y
    abel
  have hfix : f ∈ fixedSpace (universalAction ρ) B := by
    intro b
    change f + principal ρ (f.val b) = f
    rw [hf b b.property, map_zero, add_zero]
  have hall := natural_fixed_of_borel (universalAction ρ) q hq i
    (principal_injective hfixed) hdisp B S hSB hmark f hfix
  have hz : f ∈ fixed (universalAction ρ) := hall
  simpa only [fixed_universalAction ρ hfixed, Submodule.mem_bot] using hz

end Representation.SL2FourNaturalBorelFixedLifting
