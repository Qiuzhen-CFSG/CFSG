module

public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.FixedModels
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# The diagram types of the two outer involution normal forms

The action on the two parabolic conjugacy classes detects parity of the
exceptional graph power. Combining this with semilinear coverage and the
cyclic outer quotient gives the exact normal form for each diagram type.
Only the relevant field or graph cocycle descent is retained as a premise.

Source: Aschbacher–Smith H.7 and 16.1.4, printed pp.389 and 1170–1173.
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
namespace SymplecticConjugatePair.Ambient.AutomorphismCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
private theorem inner_graph_preserves_iff {n : ℕ} (hF : 2 < Nat.card F) (g : Sp F) :
    PreservesDiagram (MulAut.conj g * ExceptionalGraph.graphAut ^ n) ↔ Even n := by
  let ρ := parabolicClassAction hF
  have hi : ρ (MulAut.conj g) = 1 :=
    (mem_parabolicClassAction_ker_iff hF _).mpr (inner_preservesDiagram g)
  have hsq : ρ (ExceptionalGraph.graphAut (F := F)) ^ 2 = 1 := by
    rw [← map_pow, ExceptionalGraph.graphAut_square]
    exact (mem_parabolicClassAction_ker_iff hF _).mpr (field_preservesDiagram _)
  have hne : ρ (ExceptionalGraph.graphAut (F := F)) ≠ 1 := fun h =>
    ExceptionalGraph.graphAut_not_preservesDiagram
      ((mem_parabolicClassAction_ker_iff hF _).mp h)
  rw [← mem_parabolicClassAction_ker_iff hF]
  change ρ (MulAut.conj g * ExceptionalGraph.graphAut ^ n) = 1 ↔ Even n
  rw [map_mul, map_pow, hi, one_mul]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    simp [hk, ← two_mul, pow_mul, hsq]
  · obtain ⟨k, hk⟩ := ho
    rw [hk, pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
    simp [hne]

/-- A diagram-moving involution has odd field degree and the graph-field
normal form, conditional only on the graph cocycle descent. -/
theorem moving_normal_form {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hgraph : Odd n → ∀ g : Sp F,
      g * (ExceptionalGraph.graphAut ^ n) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ n) h)⁻¹)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : ¬ PreservesDiagram a) :
    Odd n ∧ IsConj a (ExceptionalGraph.graphAut ^ n) := by
  rcases involution_inner_or_twist hF (by omega)
    SemilinearClassification.inner_field_of_preservesDiagram a hao with hi | ⟨g, hg, hc⟩
  · obtain ⟨g, _, rfl⟩ := hi
    exact (ha (inner_preservesDiagram g)).elim
  · have hcard : 2 < Nat.card F := by
      rw [hF]
      exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
    have hodd : Odd n := Nat.not_even_iff_odd.mp (fun he =>
      ha (hg ▸ (inner_graph_preserves_iff hcard g).mpr he))
    obtain ⟨h, hh⟩ := hgraph hodd g hc
    refine ⟨hodd, ?_⟩
    rw [hg]
    exact (inner_twist_isConj _ g h hh).symm

/-- A noninner diagram-preserving involution has even field degree and the
half-Frobenius normal form, conditional only on the field cocycle descent. -/
theorem preserving_outer_normal_form {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : PreservesDiagram a)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    Even n ∧ IsConj a (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2))) := by
  rcases involution_inner_or_twist hF (by omega)
    SemilinearClassification.inner_field_of_preservesDiagram a hao with hinner | ⟨g, hg, hc⟩
  · obtain ⟨g, _, rfl⟩ := hinner
    exact (hi ⟨g, rfl⟩).elim
  · have hcard : 2 < Nat.card F := by
      rw [hF]
      exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
    have he : Even n := (inner_graph_preserves_iff hcard g).mp (hg ▸ ha)
    rw [graph_pow_eq_field_of_even he] at hg hc
    obtain ⟨h, hh⟩ := hfield he g hc
    refine ⟨he, ?_⟩
    rw [hg]
    exact (inner_twist_isConj _ g h hh).symm
end SymplecticConjugatePair.Ambient.AutomorphismCentralizers
