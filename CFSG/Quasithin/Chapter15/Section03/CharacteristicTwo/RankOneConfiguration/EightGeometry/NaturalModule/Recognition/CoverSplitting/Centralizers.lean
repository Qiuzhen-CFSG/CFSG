module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting.Transfer
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Linear centralizers of the two binary A₈ modules

The A₈ action has trivial linear-automorphism centralizer on both the
seven-dimensional augmentation kernel and its six-dimensional natural quotient.
These are the concrete rigidity inputs for extending component coordinates to
the marked symmetric group in `CoverSplitting.Transfer`.

Write `pᵢⱼ = eᵢ + eⱼ`. Double transpositions `(0 1)(i j)` force a vector fixed by
the stabilizer of `p₀₁` to be a combination of `p₀₁` and the all-one vector.
On the augmentation kernel, double transitivity gives the same coefficients
for every pair; the relation `p₀₁ + p₁₂ = p₀₂` kills the constant coefficient.
On the natural quotient, the chosen double transpositions have fixed coordinates,
so an invariant class has invariant representatives, and its image is a scalar
multiple of the pair class. Injectivity forces that scalar to be one. The pairs
span the augmentation kernel, and their images span the natural quotient.

Source context: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(1), printed pp.1132–1133, and the natural-module covering discussion
I.1.5–I.1.6(1), printed p.408. The argument here computes the centralizers
directly in the permutation modules; it requires only A₈ equivariance.
-/

@[expose] public section

open Equiv BinaryPermutation

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

private def pair (i j : Fin 8) : core (Fin 8) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private lemma permute_single (g : Perm (Fin 8)) (i : Fin 8) :
    representation (Fin 8) g (Pi.single i (1 : ZMod 2)) = Pi.single (g i) 1 := by
  ext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private lemma pair_action (g : Perm (Fin 8)) (i j : Fin 8) :
    coreRepresentation (Fin 8) g (pair i j) = pair (g i) (g j) := by
  apply Subtype.ext
  change representation (Fin 8) g (Pi.single i 1 + Pi.single j 1) = _
  rw [map_add, permute_single, permute_single]
  rfl

private lemma pair_sum (v : core (Fin 8)) :
    (∑ i : Fin 8, v.val i • pair i 0) = v := by
  apply Subtype.ext
  change (∑ i, v.val i • (Pi.single i (1 : ZMod 2) + Pi.single 0 1)) = v.val
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
  have hsum : ∑ i, v.val i = 0 := v.property
  rw [hsum, zero_smul, add_zero]
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v.val

private lemma quotient_fixed_lift (g : Perm (Fin 8)) (v : Full (Fin 8))
    (h : (constants (Fin 8)).mkQ (representation (Fin 8) g v) =
      (constants (Fin 8)).mkQ v) (hfix : ∃ i, g i = i) :
    representation (Fin 8) g v = v := by
  have hmem := (Submodule.Quotient.eq (constants (Fin 8))).mp h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  obtain ⟨i, hi⟩ := hfix
  have hi' : g.symm i = i := by simpa only [hi] using g.symm_apply_apply i
  have hz : c = 0 := by
    have he := congrFun hc i
    simpa [allOne, representation_apply, hi'] using he
  rw [hz, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

private lemma stabilizer_shape (v : Full (Fin 8))
    (h : ∀ g : alternatingGroup (Fin 8),
      coreRepresentation (Fin 8) g.val (pair 0 1) = pair 0 1 →
      (∃ i, g.val i = i) → representation (Fin 8) g.val v = v) :
    ∃ c d : ZMod 2, v = c • (pair 0 1).val + d • allOne (Fin 8) := by
  have hswap (i j : Fin 8) (hi0 : i ≠ 0) (hi1 : i ≠ 1)
      (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j) :
      representation (Fin 8) (swap 0 1 * swap i j) v = v := by
    let g : alternatingGroup (Fin 8) := ⟨swap 0 1 * swap i j, by
      simp [Perm.mem_alternatingGroup, Perm.sign_swap hij]⟩
    apply h g
    · rw [pair_action]
      have hg0 : g.val 0 = 1 := by
        simp [g, Perm.mul_apply, swap_apply_of_ne_of_ne hi0.symm hj0.symm]
      have hg1 : g.val 1 = 0 := by
        simp [g, Perm.mul_apply, swap_apply_of_ne_of_ne hi1.symm hj1.symm]
      rw [hg0, hg1]
      apply Subtype.ext
      exact add_comm _ _
    · have hex : ∀ a b : Fin 8, ∃ k : Fin 8,
          k ≠ 0 ∧ k ≠ 1 ∧ k ≠ a ∧ k ≠ b := by decide
      obtain ⟨k, hk0, hk1, hki, hkj⟩ := hex i j
      exact ⟨k, by simp [g, Perm.mul_apply, swap_apply_of_ne_of_ne, hk0, hk1, hki, hkj]⟩
  have h01 : v 0 = v 1 := by
    have he := congrFun (hswap 2 3 (by decide) (by decide) (by decide) (by decide)
      (by decide)) 1
    simpa [Perm.mul_def, swap_apply_of_ne_of_ne] using he
  have hi2 (i : Fin 8) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : v i = v 2 := by
    by_cases hi : i = 2
    · rw [hi]
    have he := congrFun (hswap i 2 hi0 hi1 (by decide) (by decide) hi) 2
    simpa [Perm.mul_def, swap_apply_of_ne_of_ne] using he
  refine ⟨v 0 + v 2, v 2, ?_⟩
  ext i
  by_cases hi0 : i = 0
  · subst i
    simp [pair, allOne, CharTwo.add_self_eq_zero, add_assoc]
  by_cases hi1 : i = 1
  · subst i
    simp [pair, allOne, CharTwo.add_self_eq_zero, add_assoc, h01]
  · simp [pair, allOne, hi0, hi1, hi2 i hi0 hi1]

private lemma pair_orbit (i j : Fin 8) (hij : i ≠ j) :
    ∃ g : alternatingGroup (Fin 8), g.val 0 = i ∧ g.val 1 = j := by
  have := alternatingGroup.isMultiplyPretransitive (Fin 8)
  have ht : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 8) - 2)
      (by simp [Nat.card_eq_fintype_card]) (Nat.sub_le _ _)
  obtain ⟨g, h0, h1⟩ := (MulAction.is_two_pretransitive_iff.mp ht)
    (by decide : (0 : Fin 8) ≠ 1) hij
  exact ⟨g, h0, h1⟩

private lemma pair_self (i : Fin 8) : pair i i = 0 := by
  apply Subtype.ext
  ext k
  exact CharTwo.add_self_eq_zero _

private lemma pair_relation : pair 0 1 + pair 1 2 = pair 0 2 := by
  apply Subtype.ext
  ext k
  fin_cases k <;> simp [pair, CharTwo.add_self_eq_zero]

private lemma pair_ne_zero : pair 0 1 ≠ 0 := by
  intro h
  have he := congrArg (fun x : core (Fin 8) => x.val 0) h
  simp [pair] at he

private lemma binary_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

/-- An automorphism of the augmentation module commuting with A₈ fixes every
weight-two vector, hence is the identity. -/
theorem core_componentCentralizer_trivial :
    TrivialComponentCentralizer (BinaryPermutation.coreRepresentation (Fin 8)) := by
  intro a ha
  obtain ⟨c, d, hd⟩ := stabilizer_shape (a (pair 0 1)).val (by
    intro g hg _
    exact congrArg Subtype.val ((ha g (pair 0 1)).symm.trans (congrArg a hg)))
  have hall (i j : Fin 8) (hij : i ≠ j) :
      (a (pair i j)).val = c • (pair i j).val + d • allOne (Fin 8) := by
    obtain ⟨g, h0, h1⟩ := pair_orbit i j hij
    have hp : coreRepresentation (Fin 8) g.val (pair 0 1) = pair i j := by
      rw [pair_action, h0, h1]
    have he := congrArg Subtype.val (ha g (pair 0 1))
    rw [hp] at he
    change (a (pair i j)).val = representation (Fin 8) g.val (a (pair 0 1)).val at he
    rw [he, hd, map_add, map_smul, map_smul, permute_allOne]
    congr 2
    exact congrArg Subtype.val hp
  have hd0 : d = 0 := by
    have he := congrArg (fun v : core (Fin 8) => (a v).val) pair_relation
    change (a (pair 0 1 + pair 1 2)).val = (a (pair 0 2)).val at he
    rw [map_add] at he
    change (a (pair 0 1)).val + (a (pair 1 2)).val = (a (pair 0 2)).val at he
    rw [hall 0 1 (by decide), hall 1 2 (by decide), hall 0 2 (by decide)] at he
    have he3 := congrFun he 3
    simpa [pair, allOne, CharTwo.add_self_eq_zero] using he3.symm
  have hc1 : c = 1 := by
    rcases binary_cases c with hc | hc
    · have hz : a (pair 0 1) = 0 := by
        apply Subtype.ext
        simpa [hc, hd0] using hd
      exact (pair_ne_zero (a.injective (hz.trans a.map_zero.symm))).elim
    · exact hc
  have hpair (i j : Fin 8) : a (pair i j) = pair i j := by
    by_cases hij : i = j
    · subst j
      rw [pair_self, map_zero]
    · apply Subtype.ext
      simpa [hc1, hd0] using hall i j hij
  apply LinearEquiv.ext
  intro v
  change a v = v
  calc
    a v = a (∑ i : Fin 8, v.val i • pair i 0) := congrArg a (pair_sum v).symm
    _ = ∑ i : Fin 8, v.val i • pair i 0 := by simp only [map_sum, map_smul, hpair]
    _ = v := pair_sum v

private lemma natural_pair_ne_zero : coreToNatural (Fin 8) (pair 0 1) ≠ 0 := by
  intro h
  have hz : (constants (Fin 8)).mkQ (pair 0 1).val = 0 := congrArg Subtype.val h
  have hc := (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  have hc0 := congrFun hc 0
  have hc2 := congrFun hc 2
  have he : (1 : ZMod 2) = 0 := by
    calc
      1 = c := by simpa [allOne, pair] using hc0.symm
      _ = 0 := by simpa [allOne, pair] using hc2
  exact one_ne_zero he

/-- The A₈ centralizer in the general linear group of the six-dimensional
natural module is trivial. -/
theorem natural_componentCentralizer_trivial :
    TrivialComponentCentralizer (BinaryPermutation.naturalRepresentation (Fin 8)) := by
  intro a ha
  let q := coreToNatural (Fin 8)
  obtain ⟨w, hw⟩ := coreToNatural_surjective (a (q (pair 0 1)))
  have hstab (g : alternatingGroup (Fin 8))
      (hg : coreRepresentation (Fin 8) g.val (pair 0 1) = pair 0 1)
      (hfix : ∃ i, g.val i = i) : representation (Fin 8) g.val w.val = w.val := by
    apply quotient_fixed_lift _ _ _ hfix
    have hp : naturalRepresentation (Fin 8) g.val (q (pair 0 1)) = q (pair 0 1) := by
      rw [← coreToNatural_equivariant, hg]
    have he : naturalRepresentation (Fin 8) g.val (q w) = q w := by
      rw [hw, ← ha, hp]
    exact congrArg Subtype.val he
  obtain ⟨c, d, hd⟩ := stabilizer_shape w.val hstab
  have hq1 : (constants (Fin 8)).mkQ (allOne (Fin 8)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Set.mem_singleton _)
  have hstart : a (q (pair 0 1)) = c • q (pair 0 1) := by
    rw [← hw]
    apply Subtype.ext
    change (constants (Fin 8)).mkQ w.val = c • (constants (Fin 8)).mkQ (pair 0 1).val
    rw [hd, map_add, map_smul, map_smul, hq1, smul_zero, add_zero]
  have hc1 : c = 1 := by
    rcases binary_cases c with hc | hc
    · have hz : a (q (pair 0 1)) = 0 := by simpa [hc] using hstart
      exact (natural_pair_ne_zero (a.injective (hz.trans a.map_zero.symm))).elim
    · exact hc
  have hstart' : a (q (pair 0 1)) = q (pair 0 1) := by simpa [hc1] using hstart
  have hpair (i j : Fin 8) : a (q (pair i j)) = q (pair i j) := by
    by_cases hij : i = j
    · subst j
      rw [pair_self, map_zero, map_zero]
    obtain ⟨g, h0, h1⟩ := pair_orbit i j hij
    have hp : coreRepresentation (Fin 8) g.val (pair 0 1) = pair i j := by
      rw [pair_action, h0, h1]
    have he := ha g (q (pair 0 1))
    rw [hstart', ← coreToNatural_equivariant, hp] at he
    exact he
  apply LinearEquiv.ext
  intro v
  change a v = v
  obtain ⟨u, rfl⟩ := coreToNatural_surjective v
  calc
    a (q u) = a (q (∑ i : Fin 8, u.val i • pair i 0)) :=
      congrArg (fun x => a (q x)) (pair_sum u).symm
    _ = q (∑ i : Fin 8, u.val i • pair i 0) := by
      simp only [map_sum, map_smul, hpair]
    _ = q u := congrArg q (pair_sum u)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

end
