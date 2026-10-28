module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RootComparison
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.Symmetries
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.Parity
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RationalGeneration.FiniteFactorization

/-!
# Rational root generation for actual Spin points

For actual Spin points, Clifford parity makes every symmetry factorization even.
Over the finite coefficient field, each pair of rational symmetries is a word in
rational coordinate roots. Parameter-preserving Weyl conjugation then reduces
these words to the eight literal signed simple Spin curves.

An entrywise rational natural action descends to the finite coefficient field,
where `FiniteFactorization` supplies a symmetry factorization with rational
anisotropic vectors. Together these results prove generation for every actual
rational Spin point, including n = 1 over the eight-element coefficient field.
The final coverage theorem discharges the rational-generation premise of
`HasRootFormula.fixed_coverage`; construction of the literal root comparison
remains with the carrier assembly.

Sources: GLS3, Remarks 2.2.5 and §2.7, and §§1.10–1.12 of Chapter 1.
-/

@[expose] public section
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport
open Triality.Standard Triality.SimplyConnected
open Theory.AlgebraicGroup

variable {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
variable {n : ℕ} {hn : 0 < n}
variable (f : ExtensionField (binaryParameters n hn) →+* k)

/-- An actual rational symmetry factorization gives a rational simple-root word.
The parity premise is discharged using the given Spin point. -/
theorem mem_rationalSimpleSubgroup_of_symmetryFactorization (g : Points k)
    (as : List (AnisotropicVector (quadraticForm k)))
    (hr : ∀ a ∈ as, RationalOrthogonal.HasCoordinates f.fieldRange a.1)
    (hfac : symmetryProductPoint as = naturalAction k g) :
    g ∈ rationalSimpleSubgroup f := by
  classical
  let : Fintype (ExtensionField (binaryParameters n hn)) := Fintype.ofFinite _
  let : Fintype f.fieldRange := RingHom.fintypeFieldRange f
  apply (mem_rationalSimpleSubgroup_iff f g).mpr
  rw [← hfac]
  exact RationalOrthogonal.even_symmetryProduct_mem f.fieldRange as hr
    (symmetryFactorization_even g as hfac)

/-- The exact rational-generation contract, conditional only on rational
symmetry factorization. No component or parity assumption is added. -/
theorem rational_generation_of_symmetryFactorization
    (hfactor : ∀ g : Points k, (∀ i j, naturalMatrix k g i j ∈ f.range) →
      ∃ as : List (AnisotropicVector (quadraticForm k)),
        (∀ a ∈ as, RationalOrthogonal.HasCoordinates f.fieldRange a.1) ∧
          symmetryProductPoint as = naturalAction k g)
    (g : Points k) (hg : ∀ i j, naturalMatrix k g i j ∈ f.range) :
    g ∈ rationalSimpleSubgroup f := by
  obtain ⟨as, hr, hfac⟩ := hfactor g hg
  exact mem_rationalSimpleSubgroup_of_symmetryFactorization f g as hr hfac

/-- Every actual Spin point with entries in the cubic coefficient field is a
word in the eight literal signed simple-root curves over that same field.
Finite-field factorization supplies rational vectors, while the Spin point
supplies even Clifford parity. This includes the coefficient field GF(8). -/
theorem rational_generation (g : Points k)
    (hg : ∀ i j : Fin 4 ⊕ Fin 4, naturalMatrix k g i j ∈ f.range) :
    g ∈ rationalSimpleSubgroup f :=
  rational_generation_of_symmetryFactorization f
    (exists_rational_symmetryFactorization f) g hg

/-- Conditional coverage from a supplied rational symmetry factorization. -/
theorem HasRootFormula.fixed_coverage_of_symmetryFactorization
    {e : SplitGroup (binaryParameters n hn) →* Points k} (he : HasRootFormula f e)
    (hfactor : ∀ g : Points k, (∀ i j, naturalMatrix k g i j ∈ f.range) →
      ∃ as : List (AnisotropicVector (quadraticForm k)),
        (∀ a ∈ as, RationalOrthogonal.HasCoordinates f.fieldRange a.1) ∧
          symmetryProductPoint as = naturalAction k g)
    (g : Points k) (hg : GraphField.sigma k n g = g) : ∃ x, e x = g :=
  he.fixed_coverage (rational_generation_of_symmetryFactorization f hfactor) g hg

/-- The literal root formulas cover every graph-field fixed Spin point.
Rational generation is proved here, with no additional factorization premise. -/
theorem HasRootFormula.fixed_coverage_of_rational_generation
    {e : SplitGroup (binaryParameters n hn) →* Points k} (he : HasRootFormula f e)
    (g : Points k) (hg : GraphField.sigma k n g = g) : ∃ x, e x = g :=
  he.fixed_coverage (rational_generation f) g hg

end Triality.BinaryDegree.CarrierTransport
