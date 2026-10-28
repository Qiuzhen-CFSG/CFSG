module
public import Theory.Representation.BinaryOffender.PerfectMoved

/-!
# Noncentral invariant subspaces preserve irreducible moved sections

For a perfect actor, a noncentral invariant subspace has noncentral
commutator space. If the full moved space lies in Irr⁺, irreducibility of
its central quotient forces these commutator spaces to agree. This is the
restriction step from an omega-core module to a canonical Sylow-center span.
Source application: Aschbacher–Smith C.2.7(3)(a), pp.146–147.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A noncentral invariant subspace generates the full moved Irr⁺ member. -/
theorem moved_eq_of_noncentral_invariant
    (L : Subgroup G) [Group.IsPerfect L]
    (hi : IsIrrPlus ρ L (subspaceCommutator ρ ⊤ L))
    (U : Submodule (ZMod 2) V) (hu : L ≤ subspaceStabilizer ρ U)
    (hn : ¬ U ≤ fixedSpace ρ L) :
    subspaceCommutator ρ U L = subspaceCommutator ρ ⊤ L := by
  rcases hi.eq_or_le_fixedSpace ρ (subspaceCommutator_invariant ρ U L)
    (subspaceCommutator_mono_left ρ le_top L) with he | hc
  · exact he
  · exact (hn (le_fixedSpace_of_commutator_le_fixedSpace ρ L U hu hc)).elim

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)

/-- A faithful submodule cannot centralize a nontrivial actor. -/
theorem range_not_fixed_of_faithful_embedding
    (e : W →ₗ[ZMod 2] V) (he : Function.Injective e)
    (hact : ∀ g w, e (σ g w) = ρ g (e w))
    (hf : Function.Injective σ) (L : Subgroup G) (hne : L ≠ ⊥) :
    ¬ LinearMap.range e ≤ fixedSpace ρ L := by
  intro h
  apply hne
  apply bot_unique
  intro l hl
  apply (Subgroup.mem_bot).mpr
  apply hf
  ext w
  apply he
  rw [map_one, Module.End.one_apply, hact]
  exact h ⟨w,rfl⟩ ⟨l,hl⟩

end Representation.BinaryOffender
