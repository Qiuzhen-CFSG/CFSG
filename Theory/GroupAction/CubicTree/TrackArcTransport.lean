module

public import Theory.GroupAction.CubicTree.TrackArcs
public import Theory.GroupAction.CubicTree.TrackTranslation

/-!
# Coordinates and conjugates of track arcs

The vertex at a given position of a finite track arc has its original integer
coordinate. Conjugation by a power of the selected translation shifts the
pointwise interval fixer by twice that power. These literal transport formulas
connect the arc generation theorem to Goldschmidt's track normalizer.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.2), p.395.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace Theory.GroupAction.CubicTree.Track
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable (t : Track Γ G)

theorem arc_getVert (a : ℤ) (n k : ℕ) (hk : k ≤ n) :
    (t.arc a n).toWalk.getVert k = t.vertex (a+k) := by
  induction n generalizing a k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp only [Walk.getVert_zero, Nat.cast_zero, add_zero]
  | succ n ih =>
    cases k with
    | zero => simp only [Walk.getVert_zero, Nat.cast_zero, add_zero]
    | succ k =>
      change ((t.arc (a+1) n).toWalk.cons (t.adjacent a)).getVert (k+1) = _
      rw [Walk.getVert_cons_succ, ih _ _ (by omega)]
      congr 1
      omega

theorem segmentFixer_map_zpow (a k : ℤ) (n : ℕ) :
    (t.segmentFixer a n).map (MulAut.conj (t.translation^k)).toMonoidHom =
      t.segmentFixer (a+2*k) n := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    apply t.mem_segmentFixer.mpr
    intro i hai hin
    change (t.translation^k * g * (t.translation^k)⁻¹) • t.vertex i = t.vertex i
    rw [mul_smul, mul_smul, ← zpow_neg, t.zpow_translate,
      t.mem_segmentFixer.mp hg _ (by omega) (by omega), t.zpow_translate]
    congr 1
    omega
  · intro hg
    refine ⟨(t.translation^k)⁻¹*g*t.translation^k, ?_, ?_⟩
    · apply t.mem_segmentFixer.mpr
      intro i hai hin
      rw [mul_smul, mul_smul, t.zpow_translate,
        t.mem_segmentFixer.mp hg _ (by omega) (by omega), ← zpow_neg, t.zpow_translate]
      congr 1
      omega
    · change t.translation^k * ((t.translation^k)⁻¹*g*t.translation^k) *
        (t.translation^k)⁻¹ = g
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

end Theory.GroupAction.CubicTree.Track

