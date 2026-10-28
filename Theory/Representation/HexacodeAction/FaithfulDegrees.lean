module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration

/-!
# The faithful binary degrees of the triple cover of A₆

The checked filtration of the central Sylow coset module has simple factors
of field degrees three and nine. Every irreducible representation with the
marked central character is a quotient of this same module. Recovering the
four-element scalar field from the central cubic therefore gives binary
degree six or eighteen, without an absolute-irreducibility assumption.

Source: Aschbacher–Smith, 13.8.30, printed p.964, and K.1.3, printed p.453.
The concrete cover and finite certificate use the existing attributed ATLAS
hexacode implementation.
-/

public section
open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional

/-- The actual central coset filtration gives the two possible field degrees. -/
theorem field_finrank_three_or_nine
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (σ : Representation F Cover V) [IsIrreducible σ]
    (hs : ∀ v, σ hexEvenZ v = omega • v) :
    Module.finrank F V = 3 ∨ Module.finrank F V = 9 := by
  obtain ⟨P, hP⟩ := cosetFiltration
  obtain ⟨f, hf⟩ := exists_central_coset_quotient P P.isPGroup' σ hs
  have hn : f ≠ 0 := by
    intro hz
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := hf v
    exact hv (hw.symm.trans (congrArg (fun q => q w) hz))
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hP.finrank_mem f hn

/-- The faithful irreducible binary degrees are six and eighteen. The field
structure is constructed from the actual central operator. -/
theorem faithful_finrank_six_or_eighteen
    {V : Type*} [AddCommGroup V] [Module Bit V] [FiniteDimensional Bit V]
    (ρ : Representation Bit HexEvenAutomorphisms V)
    (hf : Function.Injective ρ) [IsIrreducible ρ] :
    Module.finrank Bit V = 6 ∨ Module.finrank Bit V = 18 := by
  let hq := scalar_quadratic ρ hf
  let := fieldModule ρ hq
  let := fieldTower ρ hq
  let := field_finite ρ hq
  let := fieldRepresentation_irreducible ρ hq
  have hd := field_finrank_three_or_nine (fieldRepresentation ρ hq)
    (fieldRepresentation_scalar ρ hq)
  have ht := field_finrank ρ hq
  omega

end Representation.Hexacode.TwelveDimensional
