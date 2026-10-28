module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear
import Mathlib.Tactic

/-!
# The natural-to-natural square-map alternative

An equivariant self-map of the binary natural three-space that fixes zero is
zero or the identity. Two explicit transvections determine its value on a
basis vector, and transitivity determines its other values. In particular,
such a map is additive. If it describes literal group squares through a
marked kernel, the group is commutative.

This also handles the one-factor alternative of MS93 (1993), (4.6.11),
printed p.909, before a duality marking has been established. It proves the
commutativity needed for that contradiction without assuming that the
one-factor quotient is already dual or that all squares are one.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
open Matrix

theorem natural_orbit {v w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : S, g.val.mulVec v = w := by
  obtain ⟨g, hg⟩ := dual_orbit hv hw
  exact ⟨g⁻¹.transpose, hg⟩

private def e : W := ![1, 0, 0]
private def t₁ : S := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
private def t₂ : S := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

private theorem fixed_certificate : ∀ w : W,
    t₁.val.mulVec w = w → t₂.val.mulVec w = w → w = 0 ∨ w = e := by
  decide +kernel

theorem equivariantNaturalMap_zero_or_id (f : W → W) (hzero : f 0 = 0)
    (hf : ∀ (g : S) (v : W), f (g.val.mulVec v) = g.val.mulVec (f v)) :
    (∀ v, f v = 0) ∨ (∀ v, f v = v) := by
  have h₁ := hf t₁ e
  have h₂ := hf t₂ e
  rw [show t₁.val.mulVec e = e by decide] at h₁
  rw [show t₂.val.mulVec e = e by decide] at h₂
  rcases fixed_certificate (f e) h₁.symm h₂.symm with he | he
  · left
    intro v
    by_cases hv : v = 0
    · simpa only [hv] using hzero
    obtain ⟨g, hg⟩ := natural_orbit (by decide : e ≠ 0) hv
    rw [← hg, hf, he, Matrix.mulVec_zero]
  · right
    intro v
    by_cases hv : v = 0
    · simpa only [hv] using hzero
    obtain ⟨g, hg⟩ := natural_orbit (by decide : e ≠ 0) hv
    rw [← hg, hf, he]

theorem equivariantNaturalMap_add (f : W → W) (hzero : f 0 = 0)
    (hf : ∀ (g : S) (v : W), f (g.val.mulVec v) = g.val.mulVec (f v))
    (v w : W) : f (v + w) = f v + f w := by
  rcases equivariantNaturalMap_zero_or_id f hzero hf with h | h
  · rw [h, h, h, add_zero]
  · rw [h, h, h]

open Subgroup in
theorem commutative_of_natural_square_map {G : Type*} [Group G]
    (q : G →* Multiplicative W) (K : Subgroup G)
    (coordinates : K ≃* Multiplicative W) (hmem : ∀ x : G, x ^ 2 ∈ K)
    (f : W → W)
    (hsquare : ∀ x : G, f (q x).toAdd = (coordinates ⟨x ^ 2, hmem x⟩).toAdd)
    (hf : ∀ (g : S) (v : W), f (g.val.mulVec v) = g.val.mulVec (f v))
    (x y : G) : x * y = y * x := by
  have hf0 : f 0 = 0 := by
    have h := hsquare 1
    have h1 : (⟨(1 : G) ^ 2, hmem 1⟩ : K) = 1 := Subtype.ext (one_pow 2)
    rw [q.map_one, h1, coordinates.map_one] at h
    exact h
  have hs : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
    have he : coordinates ⟨(x * y) ^ 2, hmem (x * y)⟩ =
        coordinates ((⟨x ^ 2, hmem x⟩ : K) * ⟨y ^ 2, hmem y⟩) := by
      apply (show Function.Injective (@Multiplicative.toAdd W) from fun _ _ h => h)
      rw [coordinates.map_mul, toAdd_mul, ← hsquare, ← hsquare, ← hsquare,
        q.map_mul, toAdd_mul]
      exact equivariantNaturalMap_add f hf0 hf _ _
    exact congrArg Subtype.val (coordinates.injective he)
  symm
  calc
    y * x = x⁻¹ * (x * y) ^ 2 * y⁻¹ := by simp only [pow_two]; group
    _ = x⁻¹ * (x ^ 2 * y ^ 2) * y⁻¹ := by rw [hs]
    _ = x * y := by simp only [pow_two]; group

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
