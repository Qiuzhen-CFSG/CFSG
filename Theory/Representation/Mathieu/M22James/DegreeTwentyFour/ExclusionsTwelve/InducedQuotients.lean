module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.Induction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.Coordinates
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration
public import Theory.Representation.FactorDegreeFiltration

/-!
# Excluding degree twenty-four from the two fixed induced modules

The checked transversal equivalence connects the actual induced point actions
to their 66-dimensional F₄ coordinate models. A finite filtration with simple
binary factors of dimensions 12, 30 and 90 excludes every simple binary quotient
of dimension 24: a nonzero quotient map first becomes nonzero on one simple
factor, and hence identifies the target with that factor. The existing
`FactorDegreeFiltration.finrank_mem` proves this without splitting extensions.

The checked natural and dual filtrations discharge both cases of
`inducedQuotientExclusion`. Thus every intertwining map from either actual
induced point module to a simple binary representation of dimension 24 is zero.
The proof retains the nonsplit extensions and assumes no full-group degree
catalogue. It supplies the finite-module input to the published induction reduction.
Source context: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16 and Theorem 6.6/Table 6.7.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
open Representation Representation.SL3FourLocalCatalogue
universe u

/-- A concrete coordinate filtration discharges the exact induced-quotient contract. -/
theorem inducedQuotientExclusion_of_filtration (a : Constituent)
    (h : FactorDegreeFiltration ({12, 30, 90} : Set ℕ)
      (InducedCoordinates.representation a)) : InducedQuotientExclusion.{u} a := by
  intro V _ _ _ ρ hi hd f
  let := hi
  by_contra hf
  let q := f.comp (InducedCoordinates.equiv a).symm.toIntertwiningMap
  have hq : q ≠ 0 := by
    intro hz
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun t : IntertwiningMap (InducedCoordinates.representation a) ρ =>
      t (InducedCoordinates.equiv a x)) hz
    simpa [q] using hx
  have hm := h.finrank_mem q hq
  rw [hd] at hm
  norm_num at hm

/-- Neither of the two actual induced point modules has a simple binary quotient
of degree twenty-four. The concrete filtrations supply every required premise. -/
theorem inducedQuotientExclusion (a : Constituent) : InducedQuotientExclusion.{u} a := by
  apply inducedQuotientExclusion_of_filtration
  cases a with
  | natural => exact InducedCoordinates.natural_factorDegreeFiltration
  | dual => exact InducedCoordinates.dual_factorDegreeFiltration

/-- Application to both point-filtration branches of the original binary representation. -/
theorem binary_exclusion_of_induced_filtrations
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]
    (h : ∀ a, FactorDegreeFiltration ({12, 30, 90} : Set ℕ)
      (InducedCoordinates.representation a))
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 24) : False :=
  binary_exclusion_of_induced ρ (fun a => inducedQuotientExclusion_of_filtration a (h a)) hf hd

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
