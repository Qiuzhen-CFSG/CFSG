module

public import Theory.Mathieu.M12.A5Fixer.Automorphisms.LocalInputs
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.SylowCertificate
public import Theory.Mathieu.M12.Properties.SylowFixedActions

/-!
# Bounding the full automorphism stabilizer of an M₁₂ Sylow subgroup

Restriction to the marked 64-element Sylow subgroup has kernel of order at
most two, by the existing intrinsic pointwise-fixer calculation. Its image is
bounded by the 64 generator-image triples in `SylowCertificate`. Every
abstract M₁₂ automorphism preserves both certified conjugacy relations, so
the finite bound applies equally to inner and outer automorphisms.

The word-coordinate transport lemmas follow the existing exponent proof in
`Properties.SylowAutomorphismGroup`. No assertion that all candidate triples
extend to automorphisms is needed. Multiplying the kernel and image bounds
gives order at most 128 for the full setwise stabilizer.

Source context: Aschbacher–Smith 16.1.5(4) and 16.3.5, combined manuscript
of 1 March 2004, printed pp.1171 and 1178–1179.
-/

public section
namespace Sporadic.Mathieu.M12A5Fixer.Automorphisms
open Subgroup M12SmallPair M12SmallPair.SylowAutomorphismGroup
open scoped Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

private noncomputable def restriction : sylowStabilizer →* MulAut sylowCandidate :=
  { toFun := fun a => (a.val.subgroupMap sylowCandidate).trans
      (MulEquiv.subgroupCongr a.property)
    map_one' := by ext x; rfl
    map_mul' := by intro a b; ext x; rfl }

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


private theorem support_eq_of_isConj {x y : M12} (h : IsConj x y) :
    (x : Equiv.Perm (Fin 12)).support.card = (y : Equiv.Perm (Fin 12)).support.card := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he := congrArg (fun x : M12 => (x : Equiv.Perm (Fin 12)).support.card) hg
  change ((g : Equiv.Perm (Fin 12)) * (x : Equiv.Perm (Fin 12)) *
    (g : Equiv.Perm (Fin 12))⁻¹).support.card = _ at he
  rwa [Equiv.Perm.card_support_conj] at he

private def candidateGenerator (i : Fin 64) (j : Fin 3) : Fin 64 :=
  ![(SylowCertificate.candidates i).1,
    (SylowCertificate.candidates i).2.1, (SylowCertificate.candidates i).2.2] j

private theorem restriction_candidates (t : sylowStabilizer) :
    ∃ i : Fin 64, ∀ j : Fin 3,
      restriction t (generator j) = element (candidateGenerator i j) := by
  let f := restriction t
  obtain ⟨a, ha⟩ := element_surjective (f (element 1))
  obtain ⟨b, hb⟩ := element_surjective (f (element 2))
  obtain ⟨c, hc⟩ := element_surjective (f (element 3))
  have h : ∀ j : Fin 3, element (![a,b,c] j) = f (generator j) := by
    intro j
    fin_cases j
    · exact ha.trans (congrArg f (element_generator 0))
    · exact hb.trans (congrArg f (element_generator 1))
    · exact hc.trans (congrArg f (element_generator 2))
  have hfusion {i j : Fin 64} (hij : IsConj (element i : M12) (element j : M12)) :
      SylowCertificate.supportSize (substitute a b c i) =
        SylowCertificate.supportSize (substitute a b c j) := by
    rw [SylowCertificate.supportSize_eq, SylowCertificate.supportSize_eq,
      element_substitute f a b c h, element_substitute f a b c h]
    exact support_eq_of_isConj (t.val.toMonoidHom.map_isConj hij)
  obtain ⟨i, hi⟩ := SylowCertificate.candidate_coverage a b c
    (admissible_of_aut f a b c ha hb hc)
    (hfusion SylowCertificate.first_fusion) (hfusion SylowCertificate.second_fusion)
  refine ⟨i, fun j => ?_⟩
  simpa only [candidateGenerator, hi] using (h j).symm

private theorem restriction_range_card : Nat.card restriction.range ≤ 64 := by
  classical
  have hex (f : restriction.range) : ∃ i : Fin 64, ∀ j : Fin 3,
      f.val (generator j) = element (candidateGenerator i j) := by
    obtain ⟨t, ht⟩ := f.property
    rw [← ht]
    exact restriction_candidates t
  let code (f : restriction.range) : Fin 64 := (hex f).choose
  have hcode : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    apply MulEquiv.toMonoidHom_injective
    apply hom_ext
    intro j
    exact (hex f).choose_spec j |>.trans
      ((congrArg (fun i => element (candidateGenerator i j)) hfg).trans
        ((hex g).choose_spec j).symm)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective code hcode

private theorem restriction_kernel_card : Nat.card restriction.ker ≤ 2 := by
  let ρ := sylowStabilizer.subtype.comp restriction.ker.subtype
  apply m12_faithful_sylow_fixed_action_card_le_two commonSylow ρ
    (Subtype.val_injective.comp Subtype.val_injective)
  intro a x
  have ha : restriction a.val = 1 := a.property
  exact congrArg (fun f : MulAut sylowCandidate => (f x : M12)) ha

/-- The full abstract automorphism stabilizer of the marked Sylow subgroup
has order at most 128. Its restriction has at most 64 values and kernel at most two. -/
theorem sylowStabilizer_bound : SylowStabilizerBound := by
  have hcard := restriction.ker.card_mul_index
  rw [index_ker] at hcard
  exact hcard.symm.trans_le (by
    have h := Nat.mul_le_mul restriction_kernel_card restriction_range_card
    exact h)

end Sporadic.Mathieu.M12A5Fixer.Automorphisms
