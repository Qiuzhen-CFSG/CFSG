module
public import Theory.Representation.BinaryPermutation.AlternatingEightSylowFixed
public import Theory.Representation.SL2FourNaturalBorelFixedLifting.Gaschutz

/-!
# Sylow fixed vectors above the seven-dimensional alternating core

For any extension with trivial quotient by the A₈ augmentation core,
a Sylow-fixed vector has a globally fixed representative modulo that core.
Its remaining core coordinate is constant by the concrete Sylow calculation,
so the whole vector is globally fixed. No splitting of the core is assumed.

Source application: Aschbacher--Smith 15.1.27(1)--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation
variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V]
/-- A module with trivial quotient by the seven-dimensional A8 core has no
Sylow-fixed vectors beyond its globally fixed vectors. -/
theorem fixedSpace_le_invariants_of_core_subrepresentation
    (σ : Representation (ZMod 2) H V) (N : Subrepresentation σ)
    (hd : ∀ g v, σ g v - v ∈ N.toSubmodule)
    (actor : H ≃* alternatingGroup (Fin 8))
    (e : N.toSubmodule ≃ₗ[ZMod 2] core (Fin 8))
    (he : ∀ g v, e (N.toRepresentation g v) =
      alternatingCoreRepresentation (Fin 8) (actor g) (e v))
    (R : Sylow 2 H) : fixedSpace σ R ≤ σ.invariants := by
  intro v hv
  obtain ⟨c,hc,hn⟩ := SL2FourNaturalBorelFixedLifting.exists_fixed_lift
    σ N.toSubmodule hd R v hv
  let u : N.toSubmodule := ⟨v - c,hn⟩
  let R' := R.mapSurjective (f := actor.toMonoidHom) actor.surjective
  have hfix : ∀ a ∈ (R' : Subgroup (alternatingGroup (Fin 8))),
      alternatingCoreRepresentation (Fin 8) a (e u) = e u := by
    rintro a ⟨g,hg,rfl⟩
    change alternatingCoreRepresentation (Fin 8) (actor g) (e u) = e u
    rw [← he]
    congr 1
    apply Subtype.ext
    change σ g (v - c) = v - c
    have hv' : σ g v = v := hv ⟨g,hg⟩
    rw [map_sub, hv', hc g]
  have hconstant := alternatingEight_core_sylow_fixed_constant R' (e u) hfix
  intro g
  have hh : N.toRepresentation g u = u := by
    apply e.injective
    rw [he]
    exact (core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 8)) (e u)).mpr
      hconstant (actor g)
  have hh' := congrArg Subtype.val hh
  change σ g (v - c) = v - c at hh'
  rw [map_sub, hc g] at hh'
  exact sub_left_injective hh'
end BinaryPermutation
