module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.CoordinateReduction
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Sections

/-!
# Two concrete transports for the Ree D-involution calculation

The first transport removes the two left endpoint coordinates of a square-one
D word. The second compresses the five-dimensional elementary tail to
x₄(b)y₅(c)y₃(e). Both contracts require an actual conjugating element of the
fixed Ree model. Neither contract assumes root conjugacy or a class count.

Unique positive coordinates and the proved square calculation already identify
all square-one elements of D₂ with the tail, including the identity. These
results supply the coordinate interface for the two independent transports;
`DConjugacy` retains their final assembly and discharge.

Source: GLS3 Table 2.4, 2.4.5(d), and Lemma 3.3.9; Guralnick--Malle,
*Classification of 2F-modules, II*, Lemma 8.8, internal p.57.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent

namespace DConjugacy

/-- Remove the left endpoints by conjugation in the actual fixed model. -/
def TransportToD₂ (m : ℕ) : Prop :=
  ∀ p : PositiveParameters m, DSupport p → wordElement m p ^ 2 = 1 →
    ∃ (g : Model m) (q : PositiveParameters m), D₂Support q ∧
      g * wordElement m p * g⁻¹ = wordElement m q

/-- Compress the elementary tail to its middle three root curves. -/
def CompressTail (m : ℕ) : Prop :=
  ∀ v : Fin 5 → CoefficientField m,
    ∃ (g : Model m) (b c e : CoefficientField m),
      g * tailElement m v * g⁻¹ = tailElement m ![0, b, c, 0, e]

/-- The five-coordinate tail is contained in the literal D₂ subgroup. -/
theorem tailElement_mem_D₂ (m : ℕ) (v : Fin 5 → CoefficientField m) :
    tailElement m v ∈ D₂ m := by
  apply wordElement_mem_D₂
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-- Exact, unique tail coordinates for the square-one elements of D₂. -/
theorem existsUnique_tail_of_mem_D₂_sq (m : ℕ) (hm : 1 ≤ m)
    (x : Model m) (hx : x ∈ D₂ m) (hsq : x ^ 2 = 1) :
    ∃! v : Fin 5 → CoefficientField m, tailElement m v = x := by
  obtain ⟨p, hp, rfl⟩ := (sectionFacts m hm).support_D₂ x hx
  refine ⟨![p.pair 2, p.pair 3, p.central 1, p.central 2, p.central 3],
    (wordElement_eq_tail_of_D₂Support_sq m p hp hsq).symm, ?_⟩
  intro v hv
  apply tailElement_injective m
  exact hv.trans (wordElement_eq_tail_of_D₂Support_sq m p hp hsq)

/-- Membership and squaring, with no coordinate-support assumption left. -/
theorem mem_D₂_and_sq_iff (m : ℕ) (hm : 1 ≤ m) (x : Model m) :
    (x ∈ D₂ m ∧ x ^ 2 = 1) ↔ ∃ v, tailElement m v = x := by
  constructor
  · rintro ⟨hx, hsq⟩
    exact (existsUnique_tail_of_mem_D₂_sq m hm x hx hsq).exists
  · rintro ⟨v, rfl⟩
    exact ⟨tailElement_mem_D₂ m v, tailElement_sq m v⟩

end DConjugacy
end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
