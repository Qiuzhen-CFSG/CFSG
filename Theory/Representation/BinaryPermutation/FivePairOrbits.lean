module
public import Theory.Representation.BinaryPermutation.FivePairFixedSpaces
public import Theory.Representation.BinaryPermutation.FiveAction

/-!
# Every deleted five-point vector meets the pair fixed plane

The common fixed plane of two disjoint transpositions contains a weight-two
and a weight-four word. Alternating-five transitivity on each quadratic value
therefore puts every vector in that plane. The same assertion holds for every
conjugate pair group and for the literal deleted-permutation quotient.

Source: Aschbacher–Smith, 10.2.9(1), printed p.750, case (2) of 10.1.1.
-/

@[expose] public noncomputable section
open Subgroup
namespace BinaryPermutation.FivePairFixedSpaces
local instance fivePairOrbitsCoreDecidable : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance fivePairOrbitsSpaceFintype : Fintype Space := Subtype.fintype _

private def representative (b : ZMod 2) : Space :=
  ⟨![1, 1, b, b, 0], (by
    have h : ∀ b : ZMod 2, ![1, 1, b, b, 0] ∈ core (Fin 5) := by decide +kernel
    exact h b)⟩

private theorem even_orbit_meets_pair_fixed (v : Space) :
    ∃ g : alternatingGroup (Fin 5),
      coreRepresentation (Fin 5) first (coreRepresentation (Fin 5) g.val v) =
        coreRepresentation (Fin 5) g.val v ∧
      coreRepresentation (Fin 5) second (coreRepresentation (Fin 5) g.val v) =
        coreRepresentation (Fin 5) g.val v := by
  by_cases hv : v = 0
  · subst v
    exact ⟨1, by simp, by simp⟩
  have hrep : ∀ v : Space, ∃ b : ZMod 2,
      FiveGeometry.form v = FiveGeometry.form (representative b) := by decide +kernel
  obtain ⟨b, hb⟩ := hrep v
  have hne : ∀ b : ZMod 2, representative b ≠ 0 := by decide +kernel
  obtain ⟨g, hg⟩ := FiveGeometry.exists_even_transport v (representative b) hv (hne b) hb
  refine ⟨g, ?_, ?_⟩ <;> rw [hg]
  · exact (show ∀ b : ZMod 2,
      coreRepresentation (Fin 5) first (representative b) = representative b by decide +kernel) b
  · exact (show ∀ b : ZMod 2,
      coreRepresentation (Fin 5) second (representative b) = representative b by decide +kernel) b

theorem exists_even_moves_to_pair_fixed (v : Space) :
    ∃ g : alternatingGroup (Fin 5), ∀ p ∈ pairClosure,
      coreRepresentation (Fin 5) p (coreRepresentation (Fin 5) g.val v) =
        coreRepresentation (Fin 5) g.val v := by
  obtain ⟨g, hg₁, hg₂⟩ := even_orbit_meets_pair_fixed v
  refine ⟨g, ?_⟩
  intro p hp
  rcases (mem_pairClosure p).mp hp with rfl | rfl | rfl | rfl
  · simp
  · exact hg₁
  · exact hg₂
  · rw [map_mul, Module.End.mul_apply, hg₂, hg₁]

theorem exists_even_moves_to_conjugate_pair_fixed (a : Perm) (v : Space) :
    ∃ g : alternatingGroup (Fin 5),
      ∀ p ∈ pairClosure.map (MulAut.conj a).toMonoidHom,
        coreRepresentation (Fin 5) p (coreRepresentation (Fin 5) g.val v) =
          coreRepresentation (Fin 5) g.val v := by
  obtain ⟨g, hg⟩ := exists_even_moves_to_pair_fixed (coreRepresentation (Fin 5) a⁻¹ v)
  have heven : a * g.val * a⁻¹ ∈ alternatingGroup (Fin 5) := by
    exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem _ g.property _
  refine ⟨⟨a * g.val * a⁻¹, heven⟩, ?_⟩
  rintro p ⟨p, hp, rfl⟩
  change coreRepresentation (Fin 5) (a * p * a⁻¹)
    (coreRepresentation (Fin 5) (a * g.val * a⁻¹) v) = _
  have hi (w : Space) : coreRepresentation (Fin 5) a⁻¹
      (coreRepresentation (Fin 5) a w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [map_mul, Module.End.mul_apply, hi]
  rw [hg p hp]

theorem exists_even_moves_to_conjugate_pair_fixed_natural (a : Perm)
    (v : natural (Fin 5)) :
    ∃ g : alternatingGroup (Fin 5),
      ∀ p ∈ pairClosure.map (MulAut.conj a).toMonoidHom,
        naturalRepresentation (Fin 5) p (naturalRepresentation (Fin 5) g.val v) =
          naturalRepresentation (Fin 5) g.val v := by
  let E := coreEquivNatural (Fin 5) (by decide)
  obtain ⟨g, hg⟩ := exists_even_moves_to_conjugate_pair_fixed a (E.symm v)
  refine ⟨g, ?_⟩
  intro p hp
  have hh := congrArg E (hg p hp)
  simpa only [E, coreEquivNatural_equivariant, LinearEquiv.apply_symm_apply] using hh

end BinaryPermutation.FivePairFixedSpaces

