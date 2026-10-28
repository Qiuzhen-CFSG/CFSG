module

public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.IrreducibleTraceEquivalence
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual irreducibility and self-duality over a splitting field

The contragredient of a finite-dimensional irreducible group representation
is irreducible: the coannihilator of an invariant dual subspace is invariant,
and finite-dimensional annihilator duality exchanges zero and the whole space.
The annihilator argument adapts the local proof in
`Theory.Representation.PSL3Two.ResidualFFForms.Induction`.

If every group element is conjugate to its inverse, the representation and
its dual have the same trace. Irreducible trace separation then gives an
actual intertwining equivalence over an algebraically closed field, in any
characteristic. No invertibility of the group order is required. This is
the simple-module duality step used in Feit's real-valency argument,
VII.2.24 (proof p.303); the serial ordering and its reversal are separate.
-/

public section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency

/-- The finite-dimensional contragredient of an irreducible representation
is irreducible, over an arbitrary field. -/
theorem irreducible_dual {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

universe u

/-- Conjugacy to inverses makes every finite-dimensional irreducible over
an algebraically closed field actually equivalent to its contragredient. -/
theorem equiv_dual_of_isConj_inv {F V : Type u} {G : Type*}
    [Field F] [IsAlgClosed F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ]
    (hinv : ∀ g : G, IsConj g g⁻¹) : Nonempty (ρ.Equiv ρ.dual) := by
  let : IsIrreducible ρ.dual := irreducible_dual ρ
  apply (character_eq_iff_equiv_of_irreducible ρ ρ.dual).mp
  funext g
  obtain ⟨h, hh⟩ := isConj_iff.mp (hinv g)
  rw [char_dual, ← hh, char_conj]

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency
