module

public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Certificate

/-!
# The automorphism group of the marked M₁₂ Sylow subgroup is a two-group

Every automorphism of the actual 64-element subgroup `sylowCandidate`
has eighth power one. The three marked permutations generate this subgroup;
seven power tests constrain their images. The kernel-checked finite
certificate shows that substituting any permitted images eight times fixes
the generators. Preservation of multiplication transports that calculation
to an arbitrary automorphism, and generation proves that its eighth power
is the identity.

This is the local input for the M₁₂ outer-group restriction used in
Aschbacher–Smith, printed p.510, with source context GLS3, Table 5.3b.
It uses the concrete Witt-design subgroup and its checked word enumeration,
without an automorphism classification of M₁₂ or an extra model hypothesis.
-/

public section
namespace Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup

private theorem powerTest_iff (i : Fin 64) (n : ℕ) :
    powerTest i n ↔ element i ^ n = 1 ∧ element i ^ (n / 2) ≠ 1 := by
  have he (k : ℕ) : power i k = 0 ↔ element i ^ k = 1 := by
    rw [← element_injective.eq_iff, element_power, element_zero]
  exact and_congr (he n) (not_congr (he (n / 2)))

private theorem powerTest_map (f : MulAut sylowCandidate) {i j : Fin 64}
    (h : element i = f (element j)) (n : ℕ) : powerTest i n ↔ powerTest j n := by
  rw [powerTest_iff, powerTest_iff]
  have he (k : ℕ) : element i ^ k = 1 ↔ element j ^ k = 1 := by
    rw [h, ← map_pow, f.map_eq_one_iff]
  exact and_congr (he n) (not_congr (he (n / 2)))

private theorem admissible_of_aut (f : MulAut sylowCandidate) (a b c : Fin 64)
    (ha : element a = f (element 1)) (hb : element b = f (element 2))
    (hc : element c = f (element 3)) : admissible a b c := by
  have hbase : admissible 1 2 3 := by decide +kernel
  rcases hbase with ⟨h1, h2, h3, h12, h13, h23, h133⟩
  refine ⟨(powerTest_map f ha 4).mpr h1, (powerTest_map f hb 4).mpr h2,
    (powerTest_map f hc 8).mpr h3, ?_, ?_, ?_, ?_⟩
  · apply (powerTest_map f (i := multiply a b) (j := multiply 1 2) ?_ 2).mpr h12
    simp only [element_multiply, ha, hb, map_mul]
  · apply (powerTest_map f (i := multiply a c) (j := multiply 1 3) ?_ 4).mpr h13
    simp only [element_multiply, ha, hc, map_mul]
  · apply (powerTest_map f (i := multiply b c) (j := multiply 2 3) ?_ 2).mpr h23
    simp only [element_multiply, hb, hc, map_mul]
  · apply (powerTest_map f (i := multiply (multiply a c) c)
      (j := multiply (multiply 1 3) 3) ?_ 2).mpr h133
    simp only [element_multiply, ha, hc, map_mul]

private theorem element_substitute (f : MulAut sylowCandidate) (a b c : Fin 64)
    (h : ∀ j : Fin 3, element (![a,b,c] j) = f (generator j)) (i : Fin 64) :
    element (substitute a b c i) = f (element i) := by
  have hw (w : List (Fin 3)) : element (substituteWord a b c w) = f (evaluate w) := by
    induction w with
    | nil => exact element_zero.trans (map_one f).symm
    | cons j w ih => rw [substituteWord, evaluate, element_multiply, h, ih, map_mul]
  exact hw (words i)

private theorem element_repeatSubstitute (f : MulAut sylowCandidate) (a b c : Fin 64)
    (h : ∀ j : Fin 3, element (![a,b,c] j) = f (generator j)) (n : ℕ) (i : Fin 64) :
    element (repeatSubstitute a b c n i) = (f ^ n) (element i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [repeatSubstitute, element_substitute f a b c h, ih, pow_succ']
    rfl

/-- Every automorphism of the marked 64-element Sylow subgroup has eighth power one. -/
theorem pow_eight_eq_one (f : MulAut sylowCandidate) : f ^ 8 = 1 := by
  obtain ⟨a, ha⟩ := element_surjective (f (element 1))
  obtain ⟨b, hb⟩ := element_surjective (f (element 2))
  obtain ⟨c, hc⟩ := element_surjective (f (element 3))
  have h : ∀ j : Fin 3, element (![a,b,c] j) = f (generator j) := by
    intro j
    fin_cases j
    · exact ha.trans (congrArg f (element_generator 0))
    · exact hb.trans (congrArg f (element_generator 1))
    · exact hc.trans (congrArg f (element_generator 2))
  have hadm := admissible_of_aut f a b c ha hb hc
  have hf : (f ^ 8).toMonoidHom = (1 : MulAut sylowCandidate).toMonoidHom := by
    apply hom_ext
    intro j
    change (f ^ 8) (generator j) = generator j
    rw [← element_generator j, ← element_repeatSubstitute f a b c h,
      eighth_power_check a b c hadm j]
  exact MulEquiv.toMonoidHom_injective hf

/-- The full automorphism group of the actual marked Sylow two-subgroup of M₁₂ is a two-group. -/
theorem isPGroup_two : IsPGroup 2 (MulAut sylowCandidate) :=
  fun f => ⟨3, pow_eight_eq_one f⟩


end Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup
