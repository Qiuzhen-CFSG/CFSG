module
public import Theory.Representation.BinaryAlternatingFiveFlag.Coordinates

/-!
# Fixed vectors for the actual cubic between A₄ and S₃

For every cubic in the point stabilizer A₄, a fixed vector in the binary
five-point core is the sum of an A₄-fixed vector and a vector fixed by its
full A₅ normalizer. The cubic is retained literally. The two possibilities
for the first summand are zero and the standard A₄-fixed vector.

This is the translation adjustment needed to place the actual A₄ and S₃
sections in one complement in Baumeister's J₃ triangle construction.
-/

public section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension
open AlternatingFiveBorel AlternatingFiveFlag FiveCentralizerGeometry

private theorem normalizer_cubic_cases {H : Type*} [Group H]
    (s n : H) (hs : orderOf s = 3) (hn : n ∈ normalizer (zpowers s : Set H)) :
    n * s * n⁻¹ = s ∨ n * s * n⁻¹ = s⁻¹ := by
  classical
  have hfin : IsOfFinOrder s := orderOf_pos_iff.mp (by omega)
  have hsne : s ≠ 1 := by intro h; simp [h] at hs
  have hspow : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hsq : s ^ 2 = s⁻¹ := by
    apply mul_right_cancel (b := s)
    simpa [pow_succ] using hspow
  have hmem : n * s * n⁻¹ ∈ zpowers s := (hn s).mp (mem_zpowers s)
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hs] at hmem
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
  have hk3 := Finset.mem_range.mp hk
  interval_cases k
  · have he : (MulAut.conj n) s = (MulAut.conj n) 1 := by simpa using heq.symm
    exact (hsne ((MulAut.conj n).injective he)).elim
  · exact Or.inl (by simpa using heq.symm)
  · exact Or.inr (by simpa [hsq] using heq.symm)

private theorem fixed_cases : ∀ s : alternatingGroup (Fin 5),
    s ^ 3 = 1 → s ≠ 1 → s.val 4 = 4 → ∀ v : Space, act s v = v →
      (∀ n : alternatingGroup (Fin 5), n * s * n⁻¹ = s ∨ n * s * n⁻¹ = s⁻¹ →
        act n v = v) ∨
      (∀ n : alternatingGroup (Fin 5), n * s * n⁻¹ = s ∨ n * s * n⁻¹ = s⁻¹ →
        act n (v + z) = v + z) := by
  decide +kernel

/-- An actual cubic-fixed vector splits into vectors fixed by the original
point stabilizer and the full normalizer of that same cubic subgroup. -/
theorem cubic_fixed_decomposition (s : alternatingGroup (Fin 5))
    (hs : orderOf s = 3) (hB : s ∈ B) (v : core (Fin 5))
    (hv : coreRepresentation (Fin 5) s.val v = v) :
    ∃ b n : core (Fin 5), v = b + n ∧
      (∀ g : alternatingGroup (Fin 5), g ∈ B → coreRepresentation (Fin 5) g.val b = b) ∧
      (∀ g : alternatingGroup (Fin 5), g ∈ normalizer (zpowers s : Set (alternatingGroup (Fin 5))) →
        coreRepresentation (Fin 5) g.val n = n) := by
  have hpow : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hne : s ≠ 1 := by intro h; simp [h] at hs
  rcases fixed_cases s hpow hne hB v hv with hfix | hfix
  · exact ⟨0, v, (zero_add v).symm, fun g _ => map_zero _,
      fun g hg => hfix g (normalizer_cubic_cases s g hs hg)⟩
  · refine ⟨z, v + z, ?_, ?_, fun g hg => hfix g (normalizer_cubic_cases s g hs hg)⟩
    · rw [add_left_comm, show z + z = 0 by decide +kernel, add_zero]
    · intro g hg
      exact (fixes_z_iff g.val).mpr hg

set_option synthInstance.maxSize 2048 in
private theorem inverter_fixed_cases : ∀ s : alternatingGroup (Fin 5),
    s ^ 3 = 1 → s ≠ 1 → s.val 4 = 4 → ∀ t : alternatingGroup (Fin 5),
      t ^ 2 = 1 → t * s * t⁻¹ = s⁻¹ → ∀ v : Space,
        act s v = v → act t v = v → v = 0 ∨ v = act t z - z := by
  decide +kernel

/-- A vector fixed by the literal cubic and its involutory inverter is a
difference of a point-stabilizer-fixed vector. Thus the correcting translation
can preserve the entire original A₄ section while aligning the S₃ inverter. -/
theorem cubic_inverter_fixed_difference (s t : alternatingGroup (Fin 5))
    (hs : orderOf s = 3) (hB : s ∈ B) (ht : t ^ 2 = 1)
    (hi : t * s * t⁻¹ = s⁻¹) (v : core (Fin 5))
    (hsv : coreRepresentation (Fin 5) s.val v = v)
    (htv : coreRepresentation (Fin 5) t.val v = v) :
    ∃ b : core (Fin 5),
      (∀ g : alternatingGroup (Fin 5), g ∈ B → coreRepresentation (Fin 5) g.val b = b) ∧
      v = coreRepresentation (Fin 5) t.val b - b := by
  have hpow : s ^ 3 = 1 := hs ▸ pow_orderOf_eq_one s
  have hne : s ≠ 1 := by intro h; simp [h] at hs
  rcases inverter_fixed_cases s hpow hne hB t ht hi v hsv htv with hv | hv
  · exact ⟨0, fun g _ => map_zero _, by rw [map_zero, sub_zero]; exact hv⟩
  · exact ⟨z, fun g hg => (fixes_z_iff g.val).mpr hg, hv⟩

end BinaryPermutation.AlternatingFiveExtension
