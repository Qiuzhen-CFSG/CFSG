module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.ParameterRigidity.Compatibility

/-!
# Parameter rigidity of a preserved binary triality root frame

An automorphism preserving the four literal signed simple-root groups acts on
each rank-one pair by a field automorphism and reciprocal nonzero scalars.
The central coroot action on the arm root identifies the two field maps.
Surjectivity of the two root characters of the actual descended torus realizes
both scalars simultaneously. Thus one cubic coefficient automorphism and one
torus element give the automorphism's action on every signed simple root.

This proves the parameter premise of `Coverage.inner_coefficient_of_root_geometry`
without assuming common-field compatibility, diagonal innerness, global root
generation, or automorphism alignment. The last corollary uses generation only
to extend the proved root formula to the existing genuine coefficient action.

Source: Steinberg Theorem 36 and Theorem 30(2)–(4)
(`refs/KGroup/GLS3/Chapter2St1.tex`, pp.162–164 and 197–198);
GLS3 2.5.1, 2.5.8 and 2.5.12(c,d,f) (`refs/KGroup/GLS3/chapter2.tex`).
The cubic field is retained at every positive binary exponent, including one.
-/

public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage
open Parabolics ConcreteBruhat ParameterRigidity

/-- A preserved signed root frame determines one cubic field automorphism and
one element of the actual descended torus, on all four root parametrizations. -/
theorem parameters_of_preservesRootFrame (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (ha : PreservesRootFrame P hp a) :
    ∃ t ∈ torus P, ∃ e : CoefficientAut P,
      ∀ s i r, a (rootElement P hp s i r) =
        t * rootElement P hp s i (coefficientRootField P e i r) * t⁻¹ := by
  choose c e hpos hneg using exists_node_parameters P hp a ha
  have hfields := fields_compatible P hp a c e hpos hneg
  have he (i : Node) : coefficientRootField P (e .arms) i = e i := by
    cases i with
    | arms => rfl
    | central => exact hfields
  obtain ⟨t, ht, htorus⟩ := exists_torus_scalars P hp c
  refine ⟨t, ht, e .arms, ?_⟩
  intro s i r
  rw [htorus, he i]
  cases s
  · exact hneg i r
  · exact hpos i r

/-- The exact binary specialization needed by automorphism coverage, including f = 1. -/
theorem binary_parameters_of_preservesRootFrame (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (ha : PreservesRootFrame (binaryParameters f hf) rfl a) :
    ∃ t ∈ torus (binaryParameters f hf), ∃ e : CoefficientAut (binaryParameters f hf),
      ∀ s i r, a (rootElement (binaryParameters f hf) rfl s i r) =
        t * rootElement (binaryParameters f hf) rfl s i
          (coefficientRootField (binaryParameters f hf) e i r) * t⁻¹ :=
  parameters_of_preservesRootFrame _ rfl a ha

/-- Application to the existing genuine coefficient action. Global root generation
is the separate geometric premise discharged by the coverage assembly owner. -/
theorem inner_coefficient_of_preserved_root_frame (P : Parameters) (hp : P.prime = 2)
    (hgen : Subgroup.closure (rootGenerators P hp) = ⊤)
    (a : MulAut (Carrier P)) (ha : PreservesRootFrame P hp a) :
    ∃ t ∈ torus P, ∃ e : CoefficientAut P,
      a = MulAut.conj t * coefficientAction P e := by
  obtain ⟨t, ht, e, he⟩ := parameters_of_preservesRootFrame P hp a ha
  exact ⟨t, ht, e, eq_inner_coefficient_of_root_formulas P hp hgen a t e he⟩

end Triality.Standard.OuterOdd.Coverage
