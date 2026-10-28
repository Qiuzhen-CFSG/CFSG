module
public import Theory.Representation.SL2.CoreQuotientDegree
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section

/-!
# Binary degree bounds above a rank-one two-core quotient

A nontrivial representation of a finite perfect group has a nontrivial
irreducible section. The two-core acts trivially on that section, so the
actual SL₂(2ⁿ) quotient forces dimension at least 2n. The whole original
representation need not be irreducible, faithful, or trivial on the two-core.

This excludes four- and five-dimensional binary embeddings in the non-A₅
point-component comparison. Source: Aschbacher–Smith E.2.13(4), p.225,
and the embedding inspection in 10.2.9, pp.750–751.
-/

public section
open Subgroup Representation
open scoped MatrixGroups
namespace Representation.SL2
variable {H F V : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem perfect_core_quotient_finrank_bound
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    (ρ : Representation (ZMod 2) H V) (hnt : ∃ h, ρ h ≠ 1)
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2 ^ n) :
    2 * n ≤ Module.finrank (ZMod 2) V := by
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := H)).symm.toMonoidHom) (topEquiv (G := H)).symm.surjective
  have hne : ¬ (⊤ : Subgroup H) ≤ ρ.ker := by
    intro h
    obtain ⟨g,hg⟩ := hnt
    exact hg (h (mem_top g))
  obtain ⟨U,N,hi,hN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup H) hne
  let := hi
  have hntN : ∃ h, N.quotientRepresentation h ≠ 1 := by
    by_contra! he
    exact hN (fun g _ => he g)
  exact (core_quotient_irreducible_finrank_bound e N.quotientRepresentation hntN n hn hF).trans
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U.toSubmodule))
end Representation.SL2
