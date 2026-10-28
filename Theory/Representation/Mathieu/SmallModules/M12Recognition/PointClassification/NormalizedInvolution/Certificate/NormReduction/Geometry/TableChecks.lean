module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks0
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks1
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks2
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks3
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks4
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks5
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks6
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction.Geometry.Checks7
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-!
# All checked norm actions

Combine the bounded checks and expose their pointwise specifications.

Source application: Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry

theorem all_checked (i : ℕ) (hi : i < 8192) : entryCheck i = true := by
  have h : ∀ c : Fin 8,
      allBelow 8 (fun b => allBelow 128 (fun j => entryCheck (c.val*1024+b*128+j))) = true := by
    intro c
    fin_cases c
    · exact checked0
    · exact checked1
    · exact checked2
    · exact checked3
    · exact checked4
    · exact checked5
    · exact checked6
    · exact checked7
  have h₁ := (allBelow_spec _ _).mp (h ⟨i/1024, by omega⟩) ((i%1024)/128) (by omega)
  have h₂ := (allBelow_spec _ _).mp h₁ (i%128) (by omega)
  have he : i / 1024 * 1024 + i % 1024 / 128 * 128 + i % 128 = i := by omega
  simpa only [he] using h₂

theorem word_checked (i : ℕ) (hi : i < 7920) (hpos : i ≠ 0) : wordStep i = true := by
  have h := (Bool.and_eq_true_iff.mp (all_checked i (by omega))).1
  simpa only [entryCheck, if_pos (show 0 < i ∧ i < 7920 by omega)] using h

theorem seed_checked (i : ℕ) (hi : i < 7620) : seedCheck i = true := by
  have h := (Bool.and_eq_true_iff.mp (all_checked i (by omega))).2
  simpa only [entryCheck, if_pos hi] using h

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.NormReduction.Geometry
