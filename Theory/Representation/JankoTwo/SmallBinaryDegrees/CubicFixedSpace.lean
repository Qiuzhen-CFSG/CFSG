module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.Calculations
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.Scott
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.PowerConjugacy
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.RankDivisibility
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.Spectral

/-!
# The universal degree-fourteen cubic fixed-space bound

The standard pair satisfies a²=b³=(ab)⁷=1 and generates the literal carrier.
Scott's inequality bounds the sum of its three fixed dimensions by fourteen.
In characteristic two the involution fixes at least seven dimensions.
Power conjugacy forces the septic displacement to be a multiple of three,
so its fixed dimension is at least two. The cubic fixed dimension is
therefore at most five; its even displacement makes that dimension even,
and hence at most four.

The conditional reduction is retained, and `cubicFixedSpaceCalculations`
discharges both rank premises using the general spectral theorems. It proves
the universal fixed-space contract over every finite characteristic-two field.
No simplicity hypothesis or small-module completeness assertion is needed.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16, J₂ paragraph.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees
open Sporadic.LeechRelated.J2 Subgroup
open CubicFixedSpace
universe v

/-- Scott's inequality proves the required universal bound once the two
field-independent power-conjugation rank lemmas are available. -/
theorem cubicFixedSpaceCalculations_of_powerConjugacyRanks
    (hthree : PowerConjugacyRankDivisibility.{0,v} 3 2)
    (hseven : PowerConjugacyRankDivisibility.{0,v} 7 3) :
    CubicFixedSpaceCalculations.{v} := by
  intro K _ _ _ U _ _ _ τ hf hi hd
  let : τ.IsAbsolutelyIrreducible := hi
  have hirr := IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible τ
  have hnt : ∃ g, τ g ≠ 1 := by
    refine ⟨GeneratorPair.b, fun h => cubic_ne_one (hf ?_)⟩
    simpa only [map_one] using h
  have htriangle := FixedSpaceTriangle.representation_bound τ hirr hnt
    GeneratorPair.a GeneratorPair.b GeneratorPair.closure_pair_eq_top
  have hhalf := FixedSpaceTriangle.involution_half (τ GeneratorPair.a)
    (by rw [← map_pow, GeneratorPair.a_pow_two, map_one])
  have h3 := hthree K U Carrier τ GeneratorPair.b GeneratorPair.b_pow_three
    exists_conjugator_cubic_square
  have h7 := hseven K U Carrier τ (GeneratorPair.a * GeneratorPair.b)
    GeneratorPair.ab_pow_seven exists_conjugator_septic_square
  have hr3 := (τ GeneratorPair.b - 1).finrank_range_add_finrank_ker
  have hr7 := (τ (GeneratorPair.a * GeneratorPair.b) - 1).finrank_range_add_finrank_ker
  have hfixed : invariants (τ.comp (zpowers GeneratorPair.b).subtype) =
      (τ GeneratorPair.b - 1).ker := by
    ext v
    rw [mem_invariants_iff_of_forall_mem_zpowers
      (τ.comp (zpowers GeneratorPair.b).subtype)
      ⟨GeneratorPair.b, mem_zpowers _⟩ (by
        intro x
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp x.property
        exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩)]
    exact sub_eq_zero.symm
  rw [hfixed]
  obtain ⟨m, hm⟩ := h3
  obtain ⟨n, hn⟩ := h7
  omega

/-- In every faithful absolutely irreducible degree-fourteen representation
of the literal J₂ carrier over a finite characteristic-two field, the standard
cubic generator fixes at most four dimensions. This discharges the cubic
calculation used by `cubic_displacement_of_absolute_calculations`. -/
theorem cubicFixedSpaceCalculations : CubicFixedSpaceCalculations.{v} :=
  cubicFixedSpaceCalculations_of_powerConjugacyRanks
    powerConjugacyRankDivisibility_three powerConjugacyRankDivisibility_seven

end Representation.JankoTwo.SmallBinaryDegrees
