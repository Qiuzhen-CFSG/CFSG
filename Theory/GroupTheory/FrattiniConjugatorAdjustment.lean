module
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow

/-!
# Frattini adjustment with marked conjugates retained

An element normalizing a subgroup can be multiplied on the left by an
original subgroup element to normalize a prescribed Sylow subgroup.
Sylow conjugacy proves this directly. Every previously marked conjugate
normalized by that subgroup is unchanged by the adjustment.

This retains the literal crossing groups in the Frattini step of
Aschbacher--Smith 2.5.7, printed p.556; it does not require the adjusted
element to belong to the original ambient Sylow two-subgroup.
-/
public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_frattini_adjustment (N : Subgroup G) (P : Sylow p N)
    (x : G) (hx : x ∈ normalizer (N : Set G)) :
    ∃ n : N, (n : G) * x ∈ normalizer ((P : Subgroup N).map N.subtype : Set G) := by
  let e : MulAut N := N.normalizerMonoidHom ⟨x, hx⟩
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N (e • P) P
  refine ⟨n, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  have hh := congrArg (fun Q : Sylow p N => (Q : Subgroup N).map N.subtype) hn
  rw [Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def] at hh
  change (((P : Subgroup N).map e.toMonoidHom).map
    (MulAut.conj n).toMonoidHom).map N.subtype = _ at hh
  rw [map_map, map_map] at hh
  rw [map_map]
  convert hh using 1
  congr 1
  ext a
  change ((n : G) * x) * (a : G) * ((n : G) * x)⁻¹ =
    (n : G) * (x * (a : G) * x⁻¹) * (n : G)⁻¹
  simp [mul_assoc]

/-- Frattini rechoice retains every marked conjugate normalized by the
correction subgroup. -/
theorem exists_frattini_adjustment_preserving (N : Subgroup G) (P : Sylow p N)
    (x : G) (hx : x ∈ normalizer (N : Set G)) :
    ∃ y : G, y ∈ normalizer ((P : Subgroup N).map N.subtype : Set G) ∧
      (∃ n : N, y = (n : G) * x) ∧
      ∀ A : Subgroup G, N ≤ normalizer (A.conjBy x : Set G) →
        A.conjBy y = A.conjBy x := by
  obtain ⟨n, hn⟩ := exists_frattini_adjustment N P x hx
  refine ⟨n * x, hn, ⟨n, rfl⟩, ?_⟩
  intro A hA
  rw [conjBy_mul]
  exact mem_normalizer_iff_map_conj_eq.mp (hA n.property)
end Subgroup
