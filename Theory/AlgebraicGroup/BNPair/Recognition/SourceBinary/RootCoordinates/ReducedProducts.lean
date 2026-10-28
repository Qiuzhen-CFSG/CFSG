module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OppositeBorel

/-!
# Reduced products and longest-element length complementation

A left ascent extends any marked dihedral word towards the unique longest
element. Induction on the remaining distance, together with subadditivity,
shows `l(w₀w) = m - l(w)`. Borel intersections decrease along any reduced
product. These are the word and intersection inputs for Carter 2.5.7–10 in
`refs/KGroup/GLS3/Chapter2Ca2.tex`. No root system or fixed m is assumed.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

theorem length_mul_le (v w : Weyl d) :
    d.tits.wordLength (v*w) ≤ d.tits.wordLength v + d.tits.wordLength w := by
  obtain ⟨l, hlen, hl, hp⟩ := d.tits.wordLength_spec v
  obtain ⟨k, hklen, hk, hkp⟩ := d.tits.wordLength_spec w
  have h := d.tits.wordLength_le (v*w) (l++k) (by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hl s hs
    · exact hk s hs) (by rw [List.prod_append, hp, hkp])
  simpa only [List.length_append, hlen, hklen] using h

theorem length_mul_simple_le (w : Weyl d) (i : Fin 2) :
    d.tits.wordLength (w*d.simple i) ≤ d.tits.wordLength w+1 := by
  simpa only [d.tits.wordLength_mem_S (d.simple_mem i)] using length_mul_le d w (d.simple i)

theorem length_longest_mul_inv (w : Weyl d) :
    d.tits.wordLength (longest d*w⁻¹) = rotationOrder d - d.tits.wordLength w := by
  generalize hn : rotationOrder d - d.tits.wordLength w = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw : w = longest d
    · subst w
      simpa only [mul_inv_cancel, d.tits.wordLength_one, wordLength_longest, Nat.sub_self] using hn
    · obtain ⟨i, hi⟩ := exists_left_ascent d hw
      have hle := wordLength_le_rotationOrder d w
      have hle' := wordLength_le_rotationOrder d (d.simple i*w)
      have hrec := ih (rotationOrder d-d.tits.wordLength (d.simple i*w)) (by omega)
        (d.simple i*w) rfl
      have hs : (d.simple i)⁻¹ = d.simple i := inv_eq_of_mul_eq_one_right
        (by simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2)
      have hupper := length_mul_simple_le d (longest d*(d.simple i*w)⁻¹) i
      have hprod : longest d*(d.simple i*w)⁻¹*d.simple i = longest d*w⁻¹ := by
        have hss : d.simple i*d.simple i = 1 := by
          simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2
        simp only [mul_inv_rev, hs, mul_assoc, hss, mul_one]
      rw [hprod, hrec] at hupper
      have hlower := length_mul_le d (longest d*w⁻¹) w
      rw [inv_mul_cancel_right, wordLength_longest] at hlower
      omega

theorem length_longest_mul (w : Weyl d) :
    d.tits.wordLength (longest d*w) = rotationOrder d - d.tits.wordLength w := by
  simpa only [inv_inv, wordLength_inv] using length_longest_mul_inv d w⁻¹

theorem borel_intersection_reduced_mul_le (v w : Weyl d)
    (hlen : d.tits.wordLength (v*w) = d.tits.wordLength v+d.tits.wordLength w) :
    d.tits.B ⊓ borelConjugate (v*w) ≤ d.tits.B ⊓ borelConjugate w := by
  obtain ⟨l, hl, hmem, rfl⟩ := d.tits.wordLength_spec v
  rw [← hl] at hlen
  clear hl
  induction l with
  | nil => simpa only [List.prod_nil, one_mul] using (le_rfl : d.tits.B ⊓ borelConjugate w ≤ _)
  | cons s l ih =>
    have hs := hmem s (by simp)
    have hsub := length_mul_le d l.prod w
    have hlbound := d.tits.wordLength_le l.prod l (fun t ht => hmem t (by simp [ht])) rfl
    have hstep := d.tits.wordLength_mul_left_le hs (l.prod*w)
    simp only [List.prod_cons, List.length_cons, mul_assoc] at hlen
    have he : d.tits.wordLength (l.prod*w) = l.length+d.tits.wordLength w := by omega
    simp only [List.prod_cons, mul_assoc]
    exact (borel_intersection_ascent_le (T := d.tits) (s := s) (w := l.prod*w) hs (by omega)).trans
      (ih (fun t ht => hmem t (by simp [ht])) he)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
