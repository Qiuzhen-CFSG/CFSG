module

public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.PairCandidates
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.SylowPairExhaustion.Intrinsic
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.SylowPairExhaustion.Certificate

/-!
# Exhaustion of the two generator images of the Tits Sylow subgroup

Every automorphism of the actual Atlas1600 Sylow subgroup has its generator
images in the published rectangular family of 128 × 64 pairs. The unique
central involution is fixed, while the characteristic centralizer of the
second center excludes the first 1024 normal forms as images of `s8`.
The involution relation then leaves precisely the 64 second candidates.

Certified conjugators move any of these candidates to `s8`. Four preserved
relations give the 128 first candidates for an automorphism fixing `s8`.
Their set is invariant under conjugation by `s3` and `s8`, hence by the whole
Sylow subgroup using the established two-generator words. Conjugating back
therefore gives the first-image restriction for the original automorphism.

The finite certificates concern the actual permutations; two-point equality
is used only for elements already belonging to the certified Sylow subgroup.
There is no assumption of automorphism coverage or of local extension.

Source: Parrott (1972), §5, p.683, and the Atlas1600 marking described in
`refs/original/n-group-global/parrott-tits-presentation.md`. The parent local
count combines this exhaustion with its separate fusion-elimination theorem.
-/

namespace Tits.SharpOuterBound.LocalImageBound
open Subgroup ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers
open SylowPairExhaustion.Intrinsic
open SylowPairExhaustion.Certificate

private theorem gen3_perm : perm (sylowGenerator 2) = Packed.perm 4 := by
  rw [gen_perm, ← Packed.perm_eq]
  congr 1

private theorem gen8_perm : perm (sylowGenerator 7) = Packed.perm 9 := by
  rw [gen_perm, ← Packed.perm_eq]
  congr 1

private theorem eq_of_points {x y : S}
    (h0 : perm x 0 = perm y 0) (h930 : perm x 930 = perm y 930) : x = y := by
  obtain ⟨i, rfl⟩ := atlas1600SylowTwoEquiv.surjective x
  obtain ⟨j, rfl⟩ := atlas1600SylowTwoEquiv.surjective y
  apply congrArg atlas1600SylowTwoEquiv
  apply Atlas1600SylowTwoCertificate.pair_injective
  apply Prod.ext
  · simpa only [nf_perm] using h0
  · simpa only [nf_perm] using h930

private theorem second_conjugate (j : Fin 64) :
    let c := atlas1600SylowTwoEquiv (secondConjugator j)
    c * atlas1600SylowTwoEquiv (secondIndices j) = sylowGenerator 7 * c := by
  dsimp only
  apply eq_of_points
  · simpa only [map_mul, nf_perm, ← fastForm_eq, gen3_perm, gen8_perm,
      Equiv.Perm.mul_apply] using (second_conjugates j).1
  · simpa only [map_mul, nf_perm, ← fastForm_eq, gen3_perm, gen8_perm,
      Equiv.Perm.mul_apply] using (second_conjugates j).2

private def firstSet : Set S := Set.range (fun i => atlas1600SylowTwoEquiv (firstIndices i))

private theorem first_conjugate (g : Fin 2) (i : Fin 128) :
    let a := sylowGenerator (![2, 7] g)
    a * atlas1600SylowTwoEquiv (firstIndices i) =
      atlas1600SylowTwoEquiv (firstIndices (firstConjugate g i)) * a := by
  dsimp only
  have he : perm (sylowGenerator (![2, 7] g)) = conjugatingGenerator g := by
    fin_cases g
    · exact gen3_perm
    · exact gen8_perm
  apply eq_of_points
  · simpa only [map_mul, nf_perm, ← fastForm_eq, he, Equiv.Perm.mul_apply] using
      (first_conjugates g i).1
  · simpa only [map_mul, nf_perm, ← fastForm_eq, he, Equiv.Perm.mul_apply] using
      (first_conjugates g i).2

private theorem gen_normalizes (g : Fin 2) :
    sylowGenerator (![2, 7] g) ∈ normalizer firstSet := by
  let a := sylowGenerator (![2, 7] g)
  have hm : ∀ x ∈ firstSet, MulAut.conj a x ∈ firstSet := by
    rintro _ ⟨i, rfl⟩
    refine ⟨firstConjugate g i, ?_⟩
    change _ = a * atlas1600SylowTwoEquiv (firstIndices i) * a⁻¹
    rw [show a * atlas1600SylowTwoEquiv (firstIndices i) = _ from first_conjugate g i]
    simp only [a, mul_inv_cancel_right]
  let t : firstSet → firstSet := fun x => ⟨MulAut.conj a x.val, hm x.val x.property⟩
  have ht : Function.Injective t := by
    intro x y h
    exact Subtype.ext ((MulAut.conj a).injective (congrArg Subtype.val h))
  let : Finite firstSet := Set.finite_range _
  have hs := Finite.surjective_of_injective ht
  apply mem_set_normalizer_iff.mpr
  intro x
  constructor
  · exact hm x
  · intro hx
    obtain ⟨y, hy⟩ := hs ⟨_, hx⟩
    have he : y.val = x := (MulAut.conj a).injective (congrArg Subtype.val hy)
    exact he ▸ y.property

private theorem all_normalize (c : S) : c ∈ normalizer firstSet := by
  let N := normalizer firstSet
  have hx : sylowGenerator 2 ∈ N := gen_normalizes 0
  have hy : sylowGenerator 7 ∈ N := gen_normalizes 1
  obtain ⟨n, rfl⟩ := atlas1600SylowTwoEquiv.surjective c
  rw [← normalFormWord_eq]
  let x : N := ⟨_, hx⟩
  let y : N := ⟨_, hy⟩
  have h := map_normalFormWord N.subtype x y n
  exact h ▸ (normalFormWord x y n).property

private theorem perm_word_left (x y : ExceptionalParabolics.S) :
    perm (leftWord x y) = leftWord (perm x) (perm y) := by
  simp only [leftWord, map_mul, map_pow]

private theorem perm_word_right (x y : ExceptionalParabolics.S) :
    perm (rightWord x y) = rightWord (perm x) (perm y) := by
  simp only [rightWord, map_mul, map_pow]

private theorem z_fastForm : perm z = fastForm 65 := by
  rw [z_perm]
  norm_num [fastForm, Packed.perm_eq, Packed.generator,
    RelativeParabolicNormalizers.SecondCenterCertificate.x]
  rfl

private theorem generator_relations :
    sylowGenerator 2 ^ 4 = 1 ∧ sylowGenerator 7 ^ 2 = 1 ∧
    (sylowGenerator 2 * sylowGenerator 7) ^ 8 = z ∧
    leftWord (sylowGenerator 2) (sylowGenerator 7) =
      rightWord (sylowGenerator 2) (sylowGenerator 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply perm_injective
    simpa only [map_pow, map_one, gen3_perm, gen8_perm] using marked_relations.1
  · apply perm_injective
    simpa only [map_pow, map_one, gen3_perm, gen8_perm] using marked_relations.2.1
  · apply perm_injective
    simpa only [map_pow, map_mul, gen3_perm, gen8_perm, z_fastForm] using
      marked_relations.2.2.1
  · apply perm_injective
    simpa only [perm_word_left, perm_word_right, gen3_perm, gen8_perm] using
      marked_relations.2.2.2

private theorem image_relations (f : MulAut S) :
    f (sylowGenerator 2) ^ 4 = 1 ∧ f (sylowGenerator 7) ^ 2 = 1 ∧
    (f (sylowGenerator 2) * f (sylowGenerator 7)) ^ 8 = z ∧
    leftWord (f (sylowGenerator 2)) (f (sylowGenerator 7)) =
      rightWord (f (sylowGenerator 2)) (f (sylowGenerator 7)) := by
  have h := generator_relations
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg f h.1
  · simpa only [map_pow, map_one] using congrArg f h.2.1
  · simpa only [map_pow, map_mul, fixes_z] using congrArg f h.2.2.1
  · simpa only [leftWord, rightWord, map_mul, map_pow] using congrArg f h.2.2.2

private theorem second_exhaustive (f : MulAut S) :
    ∃ j : Fin 64, secondIndices j = (generatorPair f).2 := by
  let n := (generatorPair f).2
  have hn : atlas1600SylowTwoEquiv n = f (sylowGenerator 7) :=
    atlas1600SylowTwoEquiv.apply_symm_apply _
  have hs : (fastForm n ^ 2) 0 = 0 := by
    have h : atlas1600SylowTwoEquiv n ^ 2 = 1 := by
      rw [hn]
      exact (image_relations f).2.1
    have hp := congrArg perm h
    rw [map_pow, map_one, nf_perm, ← fastForm_eq] at hp
    exact congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) hp
  rcases second_candidates n with h | h | h
  · exact (image_last_not_low f n hn h).elim
  · exact (h hs).elim
  · exact ⟨secondDecode n, h⟩

private theorem first_exhaustive_fixed (f : MulAut S)
    (hy : f (sylowGenerator 7) = sylowGenerator 7) :
    ∃ i : Fin 128, firstIndices i = (generatorPair f).1 := by
  let n := (generatorPair f).1
  have hn : atlas1600SylowTwoEquiv n = f (sylowGenerator 2) :=
    atlas1600SylowTwoEquiv.apply_symm_apply _
  have hs : (fastForm n ^ 4) 0 = 0 := by
    have h : atlas1600SylowTwoEquiv n ^ 4 = 1 := by
      rw [hn]
      exact (image_relations f).1
    have hp := congrArg perm h
    rw [map_pow, map_one, nf_perm, ← fastForm_eq] at hp
    exact congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) hp
  have hp : ((fastForm n * Packed.perm 9) ^ 8) 0 = (fastForm 65) 0 := by
    have h : (atlas1600SylowTwoEquiv n * sylowGenerator 7) ^ 8 = z := by
      rw [hn, ← hy]
      exact (image_relations f).2.2.1
    have hh := congrArg perm h
    simp only [map_pow, map_mul, nf_perm, ← fastForm_eq, z_fastForm, gen8_perm] at hh
    exact congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) hh
  have hw : leftWord (fastForm n) (Packed.perm 9) 0 =
      rightWord (fastForm n) (Packed.perm 9) 0 := by
    have h : leftWord (atlas1600SylowTwoEquiv n) (sylowGenerator 7) =
        rightWord (atlas1600SylowTwoEquiv n) (sylowGenerator 7) := by
      rw [hn, ← hy]
      exact (image_relations f).2.2.2
    have hh := congrArg perm h
    simp only [perm_word_left, perm_word_right, nf_perm, ← fastForm_eq, gen8_perm] at hh
    exact congrArg (fun g : Equiv.Perm (Fin 1600) => g 0) hh
  rcases first_fixed_candidates n with h | h | h | h
  · exact ⟨firstDecode n, h⟩
  · exact (h hs).elim
  · exact (h hp).elim
  · exact (h hw).elim

private theorem first_exhaustive (f : MulAut S) :
    ∃ i : Fin 128, firstIndices i = (generatorPair f).1 := by
  obtain ⟨j, hj⟩ := second_exhaustive f
  let c := atlas1600SylowTwoEquiv (secondConjugator j)
  let f' : MulAut S := f.trans (MulAut.conj c)
  have hlast : f' (sylowGenerator 7) = sylowGenerator 7 := by
    change c * f (sylowGenerator 7) * c⁻¹ = sylowGenerator 7
    have hm : atlas1600SylowTwoEquiv (secondIndices j) = f (sylowGenerator 7) := by
      rw [hj]
      exact atlas1600SylowTwoEquiv.apply_symm_apply _
    rw [← hm, show c * atlas1600SylowTwoEquiv (secondIndices j) = _ from second_conjugate j]
    simp only [c, mul_inv_cancel_right]
  obtain ⟨i, hi⟩ := first_exhaustive_fixed f' hlast
  have hm : f' (sylowGenerator 2) ∈ firstSet := by
    refine ⟨i, ?_⟩
    change atlas1600SylowTwoEquiv (firstIndices i) = _
    rw [hi]
    exact atlas1600SylowTwoEquiv.apply_symm_apply _
  have hc := (mem_set_normalizer_iff.mp (all_normalize c) (f (sylowGenerator 2))).mpr hm
  obtain ⟨k, hk⟩ := hc
  refine ⟨k, ?_⟩
  apply atlas1600SylowTwoEquiv.injective
  exact hk.trans (atlas1600SylowTwoEquiv.apply_symm_apply _).symm

/-- Every automorphism of the marked Sylow subgroup occurs among the
published candidate image pairs. -/
public theorem generatorPair_exhaustive (f : MulAut S) :
    ∃ i : Fin 8192, candidatePair i = generatorPair f := by
  obtain ⟨i, hi⟩ := first_exhaustive f
  obtain ⟨j, hj⟩ := second_exhaustive f
  refine ⟨⟨i.val * 64 + j.val, by omega⟩, ?_⟩
  have hdiv : (i.val * 64 + j.val) / 64 = i.val := by omega
  have hmod : (i.val * 64 + j.val) % 64 = j.val := by omega
  apply Prod.ext
  · simpa only [candidatePair, hdiv] using hi
  · simpa only [candidatePair, hmod] using hj
end Tits.SharpOuterBound.LocalImageBound
