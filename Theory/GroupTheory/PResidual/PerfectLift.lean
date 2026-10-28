module

public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.IsPerfect

/-!
# Lifting perfection through a prime-group kernel

A p-perfect group mapping onto a perfect group with p-group kernel is
perfect. The kernel surjects onto the abelianization, which is therefore a
p-group; p-perfection kills that quotient. Centrality and finiteness are
not needed. This supplies the perfection step of Aschbacher--Smith C.1.8.
-/

public section
open Subgroup

theorem IsPPerfect.isPerfect_of_surjective_pGroup_kernel {E B : Type*} [Group E] [Group B]
    {p : ℕ} [Fact p.Prime] (hE : IsPPerfect p E) [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f) (hp : IsPGroup p f.ker) :
    Group.IsPerfect E := by
  have hm : (commutator E).map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  let q := QuotientGroup.mk' (commutator E)
  have hq : Function.Surjective (q.comp f.ker.subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator E) y
    obtain ⟨d, hd, hdx⟩ := (show f x ∈ (commutator E).map f by rw [hm]; trivial)
    refine ⟨⟨x * d⁻¹, ?_⟩, ?_⟩
    · simp [MonoidHom.mem_ker, hdx]
    · change q (x * d⁻¹) = q x
      have hdq : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
      simp only [map_mul, map_inv, hdq, inv_one, mul_one]
  exact ⟨hE (commutator E) inferInstance (hp.of_surjective _ hq)⟩

