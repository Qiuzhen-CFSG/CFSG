module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover.FactorData
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder

/-!
# Exact normal forms in every conjugated place

The existing first and second parabolic enumeration theorems are transported
through the literal conjugating words. Multiplication and conjugation order
are unchanged: a Sylow word comes before the rotation power.
Source: Parrott (1972), §5, p.683; FirstCover and SecondOrder.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
open ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers RelativeSecondBlockLayers

def rotation (j : Fin 38) : Atlas1600Group :=
  if j.val < 17 then atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1
  else atlas1600ParrottAssignment .s8 * atlas1600ParrottAssignment .r8

def rotationCount (j : Fin 38) : Nat := if j.val < 17 then 5 else 3

def conjugate (j : Fin 38) (x : Atlas1600Group) : Atlas1600Group :=
  placeConjugator j * x * (placeConjugator j)⁻¹

theorem conjugate_mul (j : Fin 38) (x y : Atlas1600Group) :
    conjugate j (x * y) = conjugate j x * conjugate j y := by
  simp only [conjugate]; group

theorem place_normalForm_surjective (j : Fin 38) (x : Atlas1600Group)
    (hx : x ∈ place j) :
    ∃ n : Fin 2048, ∃ e : Nat, e < rotationCount j ∧
      x = conjugate j (atlas1600SylowTwoNormalForm n * rotation j ^ e) := by
  obtain ⟨y, hy, hxy⟩ := hx
  change y ∈ placeBase j at hy
  change conjugate j y = x at hxy
  subst x
  by_cases hj : j.val < 17
  · have hy' : y ∈ first := by simpa only [placeBase, if_pos hj] using hy
    obtain ⟨⟨n, e⟩, he⟩ := firstNormalForm_surjective ⟨y, hy'⟩
    refine ⟨n, e.val, ?_, ?_⟩
    · simpa only [rotationCount, if_pos hj] using e.isLt
    · congr 1
      have hv := congrArg Subtype.val he
      simpa only [firstNormalForm_val, firstRotation, rotation, if_pos hj] using hv.symm
  · have hy' : y ∈ second := by simpa only [placeBase, if_neg hj] using hy
    obtain ⟨⟨n, e⟩, he⟩ := secondNormalForm_surjective ⟨y, hy'⟩
    refine ⟨n, e.val, ?_, ?_⟩
    · simpa only [rotationCount, if_neg hj] using e.isLt
    · congr 1
      have hv := congrArg Subtype.val he
      simpa only [secondNormalForm_val, SecondOrder.rep, rotation, if_neg hj] using hv.symm

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.CommonFactorCover
