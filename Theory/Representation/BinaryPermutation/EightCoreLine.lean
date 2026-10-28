module
public import Theory.Representation.BinaryPermutation.EightCoreNormalizer
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer

/-!
# A weight-two line from rank-one movement in the binary eight-point core

If a linear operator preserves the weight-two vectors and all its
movements lie in one nonzero line, that line has weight two. Otherwise
each pair is a sum of two fixed pairs, so the operator fixes their span,
which is the whole augmentation core. The coordinate certificate is
restricted to the pair {0,1}; permutation transport handles every pair.
Weight-two vectors also have distinct images modulo the constant line.

Source: Aschbacher--Smith, 12.6.16(2), printed pp.826--827, combined
manuscript of 1 March 2004. This model lemma retains the seven-dimensional
augmentation core, including its constant line.
-/

public section
open BinaryPermutation BinaryPermutation.EightNonsingular
set_option backward.isDefEq.respectTransparency false
namespace BinaryPermutation.EightCoreLine

private theorem avoid_base : ∀ w : Full (Fin 8), w ≠ 0 → wordWeight w ≠ 2 →
    ∃ k : Fin 8, k ≠ 0 ∧ k ≠ 1 ∧
      wordWeight ((pair 0 k).val + w) ≠ 2 ∧
      wordWeight ((pair 1 k).val + w) ≠ 2 := by
  decide +kernel

private theorem avoid_line (w : Full (Fin 8)) (hw : w ≠ 0) (hw2 : wordWeight w ≠ 2)
    (i j : Fin 8) (hij : i ≠ j) : ∃ k : Fin 8, k ≠ i ∧ k ≠ j ∧
      wordWeight ((pair i k).val + w) ≠ 2 ∧
      wordWeight ((pair j k).val + w) ≠ 2 := by
  let g := Equiv.swap (Equiv.swap 0 i 1) j * Equiv.swap 0 i
  have hg : g 0 = i ∧ g 1 = j := by
    have hh : ∀ i j : Fin 8, i ≠ j →
        (Equiv.swap (Equiv.swap 0 i 1) j * Equiv.swap 0 i) 0 = i ∧
        (Equiv.swap (Equiv.swap 0 i 1) j * Equiv.swap 0 i) 1 = j := by decide +kernel
    exact hh i j hij
  let w' := representation (Fin 8) g⁻¹ w
  have hgw : representation (Fin 8) g w' = w := by
    change (representation (Fin 8) g * representation (Fin 8) g⁻¹) w = w
    rw [←map_mul,mul_inv_cancel,map_one]
    rfl
  have hw' : w' ≠ 0 := by
    intro h
    apply hw
    rw [←hgw,h,map_zero]
  have hw2' : wordWeight w' ≠ 2 := by
    change wordWeight (representation (Fin 8) g⁻¹ w) ≠ 2
    rwa [wordWeight_permute]
  obtain ⟨k,hk0,hk1,h0,h1⟩ := avoid_base w' hw' hw2'
  have ht (a b : Fin 8) :
      wordWeight ((pair (g a) (g b)).val + w) = wordWeight ((pair a b).val + w') := by
    rw [←wordWeight_permute g ((pair a b).val + w'),map_add,hgw]
    have hh : representation (Fin 8) g (pair a b).val = (pair (g a) (g b)).val :=
      congrArg Subtype.val (pair_action g a b)
    rw [hh]
  refine ⟨g k,fun h => hk0 (g.injective (h.trans hg.1.symm)),
    fun h => hk1 (g.injective (h.trans hg.2.symm)),?_,?_⟩
  · rw [←hg.1,ht]
    exact h0
  · rw [←hg.2,ht]
    exact h1

private theorem pair_triangle (i j k : Fin 8) : pair i k + pair j k = pair i j := by
  apply Subtype.ext
  ext a
  simp only [pair, Submodule.coe_add, Pi.add_apply]
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

theorem pair_weight (i j : Fin 8) (hij : i ≠ j) :
    wordWeight (pair i j).val = 2 := by
  classical
  have hs : (Finset.univ.filter fun k => (pair i j).val k ≠ 0) = {i,j} := by
    ext k
    by_cases hki : k = i
    · subst k; simp [pair,hij,Finset.mem_filter,Pi.single_apply]
    by_cases hkj : k = j
    · subst k; simp [pair,hij.symm,Finset.mem_filter,Pi.single_apply]
    simp [pair,Pi.single_apply,hki,hkj]
  change (Finset.univ.filter _).card = 2
  rw [hs]
  simp [hij]

/-- A nontrivial rank-one displacement preserving the duads has a duad as its center. -/
theorem weight_two_of_line_displacements
    (f : core (Fin 8) →ₗ[ZMod 2] core (Fin 8)) (w : core (Fin 8)) (hw : w ≠ 0)
    (hmove : ∀ x, f x - x = 0 ∨ f x - x = w)
    (hp : ∀ i j : Fin 8, i ≠ j → wordWeight (f (pair i j)).val = 2)
    (hf : ∃ x, f x ≠ x) : wordWeight w.val = 2 := by
  by_contra hn
  have hpair (i j : Fin 8) : f (pair i j) = pair i j := by
    by_cases hij : i = j
    · subst j
      have hz : pair i i = 0 := by
        apply Subtype.ext
        ext a
        exact CharTwo.add_self_eq_zero _
      rw [hz,map_zero]
    obtain ⟨k,hki,hkj,hi,hj⟩ := avoid_line w.val (fun h => hw (Subtype.ext h)) hn i j hij
    have hfix (a : Fin 8) (hka : k ≠ a) (ha : wordWeight ((pair a k).val + w.val) ≠ 2) :
        f (pair a k) = pair a k := by
      rcases hmove (pair a k) with h | h
      · exact sub_eq_zero.mp h
      · have he : f (pair a k) = pair a k + w := by
          rw [sub_eq_iff_eq_add] at h
          exact h.trans (add_comm _ _)
        exact (ha (by change wordWeight (pair a k + w).val = 2; rw [←he]; exact hp a k hka.symm)).elim
    rw [←pair_triangle i j k,map_add,hfix i hki hi,hfix j hkj hj]
  have hsum (x : core (Fin 8)) : (∑ i, x.val i • pair i 0) = x := by
    apply Subtype.ext
    change (∑ i, x.val i • (Pi.single i 1 + Pi.single 0 1)) = x.val
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have hz : ∑ i, x.val i = 0 := x.property
    rw [hz,zero_smul,add_zero]
    simpa only [←Pi.single_smul,smul_eq_mul,mul_one] using Finset.univ_sum_single x.val
  obtain ⟨x,hx⟩ := hf
  apply hx
  conv_lhs => rw [←hsum x]
  rw [map_sum]
  simp only [map_smul,hpair]
  exact hsum x

private theorem complement_weight_two (w : Full (Fin 8)) (hw : wordWeight w = 2) :
    wordWeight (w + allOne (Fin 8)) = 6 := by
  classical
  have he : (Finset.univ.filter fun i => (w + allOne (Fin 8)) i ≠ 0) =
      (Finset.univ.filter fun i => w i ≠ 0)ᶜ := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,
      Pi.add_apply,allOne]
    have hh : ∀ a : ZMod 2, a + 1 ≠ 0 ↔ ¬ a ≠ 0 := by decide
    exact hh (w i)
  change (Finset.univ.filter _).card = 6
  rw [he,Finset.card_compl]
  change 8 - wordWeight w = 6
  rw [hw]

/-- Weight-two words are distinguished by their images modulo the constant line. -/
theorem weight_two_projection_injective (u v : core (Fin 8))
    (hu : wordWeight u.val = 2) (hv : wordWeight v.val = 2)
    (he : coreToNatural (Fin 8) u = coreToNatural (Fin 8) v) : u = v := by
  have hz : coreToNatural (Fin 8) (u-v) = 0 := by rw [map_sub,he,sub_self]
  rcases (EightGeometry.coreToNatural_eq_zero _).mp hz with h | h
  · exact sub_eq_zero.mp (Subtype.ext h)
  · have hh : u.val = v.val + allOne (Fin 8) := by
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    have hc := complement_weight_two v.val hv
    rw [←hh,hu] at hc
    contradiction

end BinaryPermutation.EightCoreLine
