module

public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Orbits and the pointwise hyperplane fixer of the binary A₅-module

Ten explicit even permutations carry a fixed weight-two or weight-four word
to every nonzero vector of the same quadratic value. This proves transitivity
on each of the two nonzero orbits without enumerating the permutation group.
The pointwise fixer of the hyperplane perpendicular to a singular point is
trivial: fixing three weight-two vectors fixes each of the five coordinates.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3, 13.2.3, and the module calculations in the
proofs of 13.3.11 and 13.6.24, printed pp.878–879, 889 and 933.
-/

public section

namespace BinaryPermutation.FiveGeometry

private def singularWord : Full (Fin 5) := ![1, 1, 1, 1, 0]
private def nonsingularWord : Full (Fin 5) := ![1, 1, 0, 0, 0]
private def cycle : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
private def interchange : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 3 4

private theorem orbit_certificate : ∀ x : Full (Fin 5),
    (∑ i, x i) = 0 → x ≠ 0 → ∃ i : Fin 5, ∃ t : Bool,
      representation (Fin 5) (cycle ^ i.val * if t then interchange else 1)
        (if (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) = 0
          then singularWord else nonsingularWord) = x := by decide

private theorem exists_even_representative (x : core (Fin 5)) (hx : x ≠ 0) :
    ∃ g : alternatingGroup (Fin 5),
      representation (Fin 5) g.val
        (if form x = 0 then singularWord else nonsingularWord) = x.val := by
  obtain ⟨i, t, hi⟩ := orbit_certificate x.val x.property (fun h => hx (Subtype.ext h))
  have hc : cycle.sign = 1 := by decide
  have hb : interchange.sign = 1 := by decide
  refine ⟨⟨cycle ^ i.val * if t then interchange else 1, ?_⟩, hi⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  cases t <;> simp [hc, hb]

/-- A₅ is transitive on the nonzero vectors of each quadratic value. -/
theorem exists_even_transport (x y : core (Fin 5)) (hx : x ≠ 0) (hy : y ≠ 0)
    (hq : form x = form y) :
    ∃ g : alternatingGroup (Fin 5), coreRepresentation (Fin 5) g.val x = y := by
  obtain ⟨a, ha⟩ := exists_even_representative x hx
  obtain ⟨b, hb⟩ := exists_even_representative y hy
  refine ⟨b * a⁻¹, Subtype.ext ?_⟩
  change representation (Fin 5) (b.val * a.val⁻¹) x.val = y.val
  rw [← ha, ← hb, hq]
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private def pairWord (j : Fin 5) : Full (Fin 5) := Pi.single 0 1 + Pi.single j 1

private theorem pair_image (g : Equiv.Perm (Fin 5)) (j : Fin 5)
    (hj : j ≠ 0) (hfix : representation (Fin 5) g (pairWord j) = pairWord j)
    (i : Fin 5) (hi : i = 0 ∨ i = j) : g i = 0 ∨ g i = j := by
  have he := congrFun hfix (g i)
  have hi1 : pairWord j i = 1 := by
    rcases hi with rfl | rfl <;> simp [pairWord, hj, Ne.symm hj]
  simp only [representation_apply, Equiv.symm_apply_apply, hi1] at he
  by_contra h
  push Not at h
  simp [pairWord, h.1, h.2] at he

/-- The pointwise fixer in S₅ of the actual marked hyperplane is trivial. -/
theorem eq_one_of_fixes_hyperplane (g : Equiv.Perm (Fin 5))
    (hfix : ∀ x : core (Fin 5), x.val 4 = 0 → coreRepresentation (Fin 5) g x = x) :
    g = 1 := by
  have hp (j : Fin 5) (hj : j ≠ 0) (hj4 : j ≠ 4) :
      representation (Fin 5) g (pairWord j) = pairWord j := by
    have hm : pairWord j ∈ core (Fin 5) := by
      simp [mem_core, pairWord, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]
    exact congrArg Subtype.val (hfix ⟨pairWord j, hm⟩ (by simp [pairWord, Ne.symm hj4]))
  have h01 := pair_image g 1 (by decide) (hp 1 (by decide) (by decide)) 0 (Or.inl rfl)
  have h02 := pair_image g 2 (by decide) (hp 2 (by decide) (by decide)) 0 (Or.inl rfl)
  have h0 : g 0 = 0 := by rcases h01 with h | h <;> rcases h02 with h' | h' <;> simp_all
  have h1 : g 1 = 1 := by
    rcases pair_image g 1 (by decide) (hp 1 (by decide) (by decide)) 1 (Or.inr rfl) with h | h
    · exact False.elim ((by decide : (1 : Fin 5) ≠ 0) (g.injective (h.trans h0.symm)))
    · exact h
  have h2 : g 2 = 2 := by
    rcases pair_image g 2 (by decide) (hp 2 (by decide) (by decide)) 2 (Or.inr rfl) with h | h
    · exact False.elim ((by decide : (2 : Fin 5) ≠ 0) (g.injective (h.trans h0.symm)))
    · exact h
  have h3 : g 3 = 3 := by
    rcases pair_image g 3 (by decide) (hp 3 (by decide) (by decide)) 3 (Or.inr rfl) with h | h
    · exact False.elim ((by decide : (3 : Fin 5) ≠ 0) (g.injective (h.trans h0.symm)))
    · exact h
  have h4 : g 4 = 4 := by
    have hn0 := g.injective.ne (by decide : (4 : Fin 5) ≠ 0)
    have hn1 := g.injective.ne (by decide : (4 : Fin 5) ≠ 1)
    have hn2 := g.injective.ne (by decide : (4 : Fin 5) ≠ 2)
    have hn3 := g.injective.ne (by decide : (4 : Fin 5) ≠ 3)
    rw [h0] at hn0
    rw [h1] at hn1
    rw [h2] at hn2
    rw [h3] at hn3
    have hall : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → i = 4 := by decide
    exact hall (g 4) hn0 hn1 hn2 hn3
  apply Equiv.ext
  intro i
  fin_cases i <;> simp_all

end BinaryPermutation.FiveGeometry
