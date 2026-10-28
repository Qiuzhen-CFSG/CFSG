module
public import Theory.Representation.BinaryPermutation.FiveAction
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Full displacement on the binary five-point augmentation module

A five-cycle has no nonzero fixed vector on the four-dimensional binary
augmentation module. Its displacement map is therefore surjective, so any
representation identified with this module through a surjective alternating
actor has zero coinvariant quotient. The actual coordinates and covering
map are retained for applications to a component acting on an extraspecial
central quotient.

Source application: Aschbacher–Smith 14.2.16, printed p.986.
-/

public noncomputable section
open Representation
namespace BinaryPermutation
private def fiveCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩

private theorem fiveCycle_fixed (v : core (Fin 5))
    (hv : coreRepresentation (Fin 5) fiveCycle.val v = v) : v = 0 := by
  have h : ∀ v : Full (Fin 5), (∑ i, v i) = 0 →
      representation (Fin 5) fiveCycle.val v = v → v = 0 := by decide +kernel
  exact Subtype.ext (h v v.property (congrArg Subtype.val hv))

/-- Full five-point coordinates force full displacement for every surjective
cover of the actual alternating actor. -/
theorem five_coinvariants_of_coordinates
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V)
    (f : A →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (c : V ≃ₗ[ZMod 2] core (Fin 5))
    (hc : ∀ a v, c (ρ a v) = coreRepresentation (Fin 5) (f a).val (c v)) :
    Coinvariants.ker ρ = ⊤ := by
  let : Finite V := Finite.of_equiv (core (Fin 5)) c.toEquiv.symm
  obtain ⟨a,ha⟩ := hf fiveCycle
  let d : V →ₗ[ZMod 2] V := ρ a - LinearMap.id
  have hi : Function.Injective d := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    change v = 0
    have hv' : ρ a v = v := sub_eq_zero.mp hv
    have he := hc a v
    rw [hv',ha] at he
    apply c.injective
    rw [map_zero]
    exact fiveCycle_fixed (c v) he.symm
  apply top_unique
  intro v _
  obtain ⟨w,hw⟩ := Finite.surjective_of_injective hi v
  have hm := Coinvariants.sub_mem_ker (ρ := ρ) a w
  exact hw ▸ hm
end BinaryPermutation
