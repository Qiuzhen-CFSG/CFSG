module

public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeData

/-!
# Positivity of the Table I weighted columns

The centralizer identity and positive group orders make the common order-two
weighted column positive. This shared interface lets the early and late
eliminations be imported together. The default column is zero, preserving the
late cases' call form as well as the early cases' explicit column argument.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4(c).
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData

/-- Lemma 4(c) forces the common order-two weighted column to be positive. -/
theorem OrderConstraints.weighted_z_pos
    {I : Type*} [Fintype I] {d : GeneralizedDecompositionData I}
    {degree : I → ℤ} {g c e : ℕ} (h : d.OrderConstraints degree g c e)
    (i : Fin 5 := 0) : 0 < d.weightedColumn degree (d.iDz i) := by
  rw [h.equal_z i]
  have hg : (0 : ℚ) < g := by exact_mod_cast h.group_pos
  have hc : (0 : ℚ) < c := by exact_mod_cast h.centralizer_pos
  have he : (0 : ℚ) < e := by exact_mod_cast h.center_centralizer_pos
  have hm : (0 : ℚ) < (g : ℚ) * e ^ 2 := mul_pos hg (sq_pos_of_pos he)
  have hp : (0 : ℚ) < 128 * (c : ℚ) ^ 3 := by positivity
  rw [← h.centralizer_identity] at hp
  exact (mul_pos_iff_of_pos_left hm).mp hp

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
