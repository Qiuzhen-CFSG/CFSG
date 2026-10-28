module

public import Theory.Character.ClassFunction
public import Theory.Character.FiniteOrderTrace

/-!
# The degree bound for the integer involution value

The trace of an operator of order dividing two has absolute value at most
its dimension. Thus an integer involution value is at most the degree.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion

theorem character_involution_value_le_degree {G : Type*} [Group G]
    {χ : ClassFunction G} (hχ : IsCharacter χ) (e b : ℤ)
    (hdegree : χ 1 = (e : ℂ)) (t : G) (ht : orderOf t = 2)
    (hvalue : χ t = (b : ℂ)) : b ≤ e := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have hp : (ρ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hb := finite_order_end_norm_trace_le_finrank (ρ t) (by decide : 2 ≠ 0) hp
  change ‖ρ.character t‖ ≤ (Module.finrank ℂ (Fin n → ℂ) : ℝ) at hb
  have hbe : (b : ℝ) ≤ (e : ℝ) := calc
    (b : ℝ) = (ρ.character t).re := by rw [hvalue]; rfl
    _ ≤ ‖ρ.character t‖ := Complex.re_le_norm _
    _ ≤ Module.finrank ℂ (Fin n → ℂ) := hb
    _ = (ρ.character 1).re := by rw [ρ.char_one]; simp only [Complex.natCast_re]
    _ = (e : ℝ) := by rw [hdegree]; rfl
  exact_mod_cast hbe

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion
