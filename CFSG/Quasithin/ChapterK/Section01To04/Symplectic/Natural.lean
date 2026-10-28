module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Setup
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFixed

/-!
# The natural parabolic offender in K.3.4

The plane radical consists of symmetric upper shears. Every displacement
lands in the plane, which the radical fixes pointwise. Thus its natural
action is quadratic. The actual fixed-space and order computations give
rank 3r, fixed dimension 2r, and ratio 2/3 on the natural binary 4r-space.

Source: Aschbacher–Smith, K.3.4.1, printed p.456. This module supplies the
upper bound and the concrete offender; the lower bound for arbitrary
actors and representation recognition remain separate obligations.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic.Natural
open scoped ENNReal Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] in
/-- Every plane-radical displacement lies in its pointwise fixed plane. -/
theorem planeRadical_displacement_mem {g : Sp F}
    (hg : g ∈ planeRadical) (v : Vector F) :
    binaryNatural g v - v ∈ (plane F).restrictScalars (ZMod 2) := by
  obtain ⟨B, rfl⟩ := (mem_planeRadical_iff g).mp hg
  intro i
  change ((Plane.shearSp B).val *ᵥ v) (.inr i) - v (.inr i) = 0
  fin_cases i <;>
    simp [Plane.shearSp, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      fromBlocks, one_apply]

/-- The concrete rank-three parabolic radical acts quadratically. -/
theorem planeRadical_quadratic :
    IsQuadratic (binaryNatural (F := F)) planeRadical := by
  intro a ha b hb v
  have hv := planeRadical_displacement_mem hb v
  rw [← planeRadical_natural_fixedSpace] at hv
  exact hv ⟨a, ha⟩

omit [Algebra (ZMod 2) F] in
/-- This radical is a nontrivial elementary actor for every positive field degree. -/
theorem planeRadical_isElementaryTwo {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r) :
    IsElementaryTwo (planeRadical (F := F)) := by
  refine ⟨?_, planeRadical_elementary⟩
  intro h
  have hh := rank_planeRadical hF
  rw [h, BinaryOffender.rank, Subgroup.card_bot] at hh
  norm_num at hh
  omega

/-- The displayed 2/3 ratio is attained by the literal plane radical. -/
theorem planeRadical_ratio {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r) :
    actionRatio (binaryNatural (F := F)) planeRadical = (2 : ℝ≥0∞) / 3 := by
  have hr0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rw [actionRatio, planeRadical_natural_fixedCodim hF, rank_planeRadical hF]
  push_cast
  exact ENNReal.mul_div_mul_right _ _ hr0 (by simp)

/-- The first quantitative conclusion of K.3.4.1. -/
theorem quadraticRatio_le_two_thirds {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r) :
    quadraticRatio (binaryNatural (F := F)) ≤ (2 : ℝ≥0∞) / 3 := by
  rw [← planeRadical_ratio hF hr]
  exact iInf_le_of_le planeRadical (iInf_le_of_le
    ⟨planeRadical_isElementaryTwo hF hr, planeRadical_quadratic⟩ le_rfl)

/-- This is an actual strong FF-offender, with its dimensions recorded. -/
theorem planeRadical_offender {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 0 < r) :
    Module.finrank (ZMod 2) (Vector F) = 4 * r ∧
      rank (planeRadical (F := F)) = 3 * r ∧
      Module.finrank (ZMod 2) (fixedSpace (binaryNatural (F := F)) planeRadical) = 2 * r ∧
      IsStrongOffender (binaryNatural (F := F)) planeRadical := by
  refine ⟨finrank_vector hF, rank_planeRadical hF, ?_, planeRadical_isElementaryTwo hF hr, ?_⟩
  · rw [planeRadical_natural_fixedSpace, finrank_binary_plane hF]
  · rw [planeRadical_natural_fixedCodim hF, rank_planeRadical hF]
    omega

end CFSG.Quasithin.ChapterK.Symplectic.Natural
