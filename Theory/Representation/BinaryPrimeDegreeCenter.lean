module

public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute.PrimeDimension
public import Theory.Representation.PGroupScalarWitness

/-!
# Trivial centers in faithful prime-dimensional binary representations

A faithful irreducible representation of prime dimension of a nonabelian
group over a finite field is absolutely irreducible. Central elements
therefore act by nonzero scalars. Over F₂ the only such scalar is one, so
faithfulness forces the center to be trivial.

This removes central covers after the degree-eleven reduction in
Aschbacher–Smith, Chapter K, printed pp.451, 457.
-/

public section
namespace Representation

/-- Prime-dimensional faithful irreducible binary representations of
nonabelian groups eliminate the entire center, including its odd part. -/
theorem center_eq_bot_of_binary_prime_finrank
    {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hp : (Module.finrank (ZMod 2) V).Prime)
    (hn : ¬ IsMulCommutative G) : Subgroup.center G = ⊥ := by
  let : ρ.IsAbsolutelyIrreducible :=
    isAbsolutelyIrreducible_of_prime_finrank_of_faithful ρ hf hp hn
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  apply le_bot_iff.mp
  intro g hg
  obtain ⟨a, ha⟩ := exists_scalar_of_mem_center_of_absolutelyIrreducible ρ g hg
  have hane : a ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply (Representation.apply_bijective ρ g).injective
    simp [ha, hz]
  have haone : a = 1 := by
    have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    exact (h a).resolve_left hane
  apply hf
  rw [ha, haone, one_smul, map_one]
  rfl

end Representation
