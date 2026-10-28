module

public import Theory.Representation.HexacodeAction.FaithfulDegrees
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SubspaceQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.ScalarCoordinates

/-!
# The corrected quotient calculation in 13.8.30

The displayed denominator in `Ŝ₃/Û_L` on printed p.964 is a misprint:
the adjacent subgroup quotient has denominator `U_H V`, and the calculation
adds one to two. Thus the denominator is the image `Û_H`, a field line.
The theorem below uses that line inside the literal span `Ŝ₃`. An element
of L₂,+ moving this span makes it proper. The checked triple-cover degree
theorem then forces dimension nine over the four-element field.

The application retains a coordinate homomorphism from the actual `U_L/W`,
with its exact kernel and conjugation action. Constructing the maximal
invariant W, faithfulness, and the tensor-span markings is still a source
obligation. This module does not assert the nine-chief-factor conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma 13.8.30, printed p.964.
-/

public section
open Subgroup Representation Atlas.Codes
open Representation.Hexacode Representation.Hexacode.TwelveDimensional
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

/-- The corrected denominator is a line inside the three-dimensional span.
Noninvariance of that span excludes field degree three. -/
theorem source_quotient_field_dimension
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F HexEvenAutomorphisms W) [IsIrreducible σ]
    (hs : ∀ w, σ hexEvenZ w = omega • w)
    (S3 : Submodule F W) (UHimage : Submodule F S3)
    (hline : Module.finrank F UHimage = 1)
    (hquotient : Module.finrank F (S3 ⧸ UHimage) = 2)
    (hmoved : ∃ g w, w ∈ S3 ∧ σ g w ∉ S3) :
    Module.finrank F W = 9 := by
  have hdim : Module.finrank F S3 = 3 := by
    have ht := UHimage.finrank_quotient_add_finrank
    omega
  have hproper : S3 ≠ ⊤ := by
    rintro rfl
    obtain ⟨g, w, _, hn⟩ := hmoved
    exact hn (Submodule.mem_top)
  have hlt := Submodule.finrank_lt hproper
  have hd := field_finrank_three_or_nine σ hs
  omega

/-- The scalar action of the actual L₀ on the maximal quotient produces nine
actual noncentral two-chief factors in every complete L₀-chief series.
`d₀` retains the intersections with L₀ and the literal quotient kernel.
Producing this section and the three tensor-span markings is separate. -/
theorem source_nine_factors_of_marked_quotient
    {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module Bit W] [Module F W] [IsScalarTower Bit F W]
    [FiniteDimensional F W]
    (L₀ UL N : Subgroup G)
    (σ : Representation F HexEvenAutomorphisms W) [IsIrreducible σ]
    (hs : ∀ w, σ hexEvenZ w = omega • w)
    (τ : Representation Bit L₀ W)
    (d₀ : BinaryConjugationSection L₀ (UL ⊓ L₀) (N ⊓ L₀) τ)
    (χ : L₀ →* Fˣ) (hχ : Function.Surjective χ) (hn : ∃ h, χ h ≠ 1)
    (hscalar : ∀ h w, τ h w = (χ h : F) • w)
    (S3 : Submodule F W) (UHimage : Submodule F S3)
    (hline : Module.finrank F UHimage = 1)
    (hquotient : Module.finrank F (S3 ⧸ UHimage) = 2)
    (hmoved : ∃ g w, w ∈ S3 ∧ σ g w ∉ S3)
    (t : NoncentralChiefRefinement.ChiefSeries L₀)
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) : 9 ≤ t.noncentralTwoCount := by
  have hd := source_quotient_field_dimension σ hs S3 UHimage hline hquotient hmoved
  have hc := NoncentralChiefRefinement.scalar_dimension_le_complete_count
    d₀ χ hχ hn hscalar t ht0 ht1
  omega

end CFSG.Quasithin.Chapter13.Section08.LinearFour
