module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.Spectral
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.CubicFixedSpace.Scott
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.VertexExtension.Eight
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NoncommRing
import Lean.Elab.Tactic.Omega

/-!
# Excluding Hall--Janko dimensions below six

The actual degree-100 carrier has a certified element of order eight. In
characteristic two its displacement operator is nilpotent, so faithfulness
forces dimension at least five. Dimension five is incompatible with Scott's
inequality for the checked generating pair a,b: their fixed dimensions are at
least three and one, and that of ab is at least two. The last two bounds use
the proved cubic and septic displacement divisibilities.

This proves the lower endpoint of the absolute small-degree window without
assuming simplicity, a finite coefficient field, or a modular catalogue.
`DegreeCompleteness` applies it after extension to an algebraic closure.

Sources: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.16, and the characteristic-two J₂ entries of corrected Hiss--Malle
Table 2. The actual order-eight word and its ATLAS attribution are retained in
`J2/RecognitionGeometry/VertexExtension/Eight.lean` and its source directory.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
open Sporadic.LeechRelated.J2

private theorem sub_one_pow_two_pow {K U : Type*} [Field K] [CharP K 2]
    [AddCommGroup U] [Module K U] (T : Module.End K U) (n : ℕ) :
    (T - 1) ^ (2 ^ n) = T ^ (2 ^ n) - 1 := by
  have htwice (A : Module.End K U) : A + A = 0 := by
    calc
      A + A = (2 : K) • A := (two_smul K A).symm
      _ = 0 := by rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_smul]
  have hneg : -(1 : Module.End K U) = 1 := by
    exact neg_eq_iff_add_eq_zero.mpr (htwice 1)
  have hsquare (A : Module.End K U) : (A - 1) ^ 2 = A ^ 2 - 1 := by
    calc
      (A - 1) ^ 2 = A ^ 2 - (A + A) + 1 := by noncomm_ring
      _ = A ^ 2 - 1 := by rw [htwice, sub_zero, sub_eq_add_neg, hneg]
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, hsquare, ← pow_mul]

/-- The certified order-eight element rules out faithful characteristic-two
representations of dimensions zero through four, without irreducibility. -/
theorem five_le_finrank_of_faithful {K U : Type*} [Field K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U) (hf : Function.Injective τ) :
    5 ≤ Module.finrank K U := by
  by_contra! hd
  let x := RecognitionGeometry.VertexExtension.eight
  have hx8 : x ^ 8 = 1 := RecognitionGeometry.VertexExtension.eight_pow_eight
  have hx4 : x ^ 4 ≠ 1 := RecognitionGeometry.VertexExtension.eight_pow_four_ne
  have h8 : (τ x - 1) ^ 8 = 0 := by
    rw [show 8 = 2 ^ 3 from rfl, sub_one_pow_two_pow]
    rw [← map_pow, show 2 ^ 3 = 8 from rfl, hx8, map_one, sub_self]
  have hnil : (τ x - 1) ^ Module.finrank K U = 0 := by
    ext u
    have hu : u ∈ ((τ x - 1) ^ 8).ker := by rw [h8]; simp
    exact (Module.End.ker_pow_le_ker_pow_finrank (τ x - 1) 8) hu
  have h4 : (τ x - 1) ^ 4 = 0 := pow_eq_zero_of_le (by omega) hnil
  rw [show 4 = 2 ^ 2 from rfl, sub_one_pow_two_pow, ← map_pow] at h4
  change τ (x ^ 4) - 1 = 0 at h4
  apply hx4
  apply hf
  simpa only [map_one] using sub_eq_zero.mp h4

open CubicFixedSpace
universe v
/-- In dimension five, the fixed dimensions of the standard involution, cubic
and septic are at least three, one and two, contradicting Scott's bound. -/
theorem finrank_ne_five_of_faithful_irreducible {K U : Type v} [Field K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U) (hf : Function.Injective τ)
    (hi : τ.IsIrreducible) : Module.finrank K U ≠ 5 := by
  intro hd
  have hnt : ∃ g, τ g ≠ 1 := by
    refine ⟨GeneratorPair.b, fun h => cubic_ne_one (hf ?_)⟩
    simpa only [map_one] using h
  have htriangle := FixedSpaceTriangle.representation_bound τ hi hnt
    GeneratorPair.a GeneratorPair.b GeneratorPair.closure_pair_eq_top
  have hhalf := FixedSpaceTriangle.involution_half (τ GeneratorPair.a)
    (by rw [← map_pow, GeneratorPair.a_pow_two, map_one])
  obtain ⟨m, hm⟩ := two_dvd_cubic_displacement_rank τ
  obtain ⟨n, hn⟩ := three_dvd_septic_displacement_rank τ
  have hr3 := (τ GeneratorPair.b - 1).finrank_range_add_finrank_ker
  have hr7 := (τ (GeneratorPair.a * GeneratorPair.b) - 1).finrank_range_add_finrank_ker
  omega

/-- Every faithful irreducible characteristic-two representation of the literal
carrier has dimension at least six. No catalogue or simplicity is used. -/
theorem six_le_finrank_of_faithful_irreducible {K U : Type v} [Field K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K Carrier U) (hf : Function.Injective τ)
    (hi : τ.IsIrreducible) : 6 ≤ Module.finrank K U := by
  have hlow := five_le_finrank_of_faithful τ hf
  have hne := finrank_ne_five_of_faithful_irreducible τ hf hi
  omega

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
