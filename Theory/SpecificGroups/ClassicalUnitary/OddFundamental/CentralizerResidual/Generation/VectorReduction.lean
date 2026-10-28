module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.PlaneRotations
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.VectorReduction.CoordinatePlanes

/-!
# Reduction of norm-one vectors by special unitary planes

Over a quadratic finite field of odd characteristic, actual coordinate-plane
SU₂ homomorphisms reduce every norm-one vector to the first basis vector.
The coefficient field and its involution are kept throughout.

Induct on the number of nonzero coordinates. If every pair of nonzero
coordinates had zero norm sum, three such coordinates would imply twice a
nonzero scalar norm is zero. Consequently at most two coordinates could
remain, contradicting total norm one. A plane rotation therefore clears one
nonzero coordinate without introducing support elsewhere. For a single
remaining coordinate, one last plane rotation moves and normalizes it.

The final theorem applies the stabilizer induction from `Generation.Reduction`
to prove that the actual SU₂ images generate SUₙ for every positive n,
including the field parameter q = 3.

Source application: Aschbacher–Smith, A.2.17, printed pp.38–39 of
`refs/quasithin.pdf`, the complementary group J* ≅ SU_{N-2}(q).
-/

public section
open Matrix BenderSuzuki.MatrixGroups
open scoped Classical
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
variable {F : Type*} [Field F] (σ : F ≃+* F)

private theorem norm_eq_pair {n : ℕ} (x : Fin n → F) (i j : Fin n) (hij : i ≠ j)
    (h : ∀ t, t ≠ i → t ≠ j → x t = 0) :
    norm σ x = σ (x i) * x i + σ (x j) * x j := by
  classical
  rw [← Finset.sum_pair (f := fun t => σ (x t) * x t) hij]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro t _ ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  have hz := h t ht.1 ht.2
  simp [hz]

private theorem exists_pair_norm_ne_zero {n : ℕ} (h2 : (2 : F) ≠ 0)
    (x : Fin n → F) (hx : norm σ x = 1)
    (hs : 1 < (Finset.univ.filter (fun i => x i ≠ 0)).card) :
    ∃ i j, i ≠ j ∧ x i ≠ 0 ∧ x j ≠ 0 ∧
      σ (x i) * x i + σ (x j) * x j ≠ 0 := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra! h
  have hab := h i j hij hi hj
  have hz (t : Fin n) (hti : t ≠ i) (htj : t ≠ j) : x t = 0 := by
    by_contra ht
    have hat := h i t hti.symm hi ht
    have hbt := h j t htj.symm hj ht
    have he : (2 : F) * (σ (x i) * x i) = 0 := by
      linear_combination hab + hat - hbt
    exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero σ).mpr hi) hi) he
  have hh := norm_eq_pair σ x i j hij hz
  rw [hx, hab] at hh
  exact one_ne_zero hh

variable (hσ : Function.Involutive σ)

private theorem reduce_single_support {n : ℕ} (x : Fin (n+2) → F)
    (hx : norm σ x = 1) (hs : (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ 1) :
    ∃ a : (form σ hσ (n+2)).specialSubgroup,
      a ∈ twoSpaceGenerated σ hσ (n+2) ∧ a.val.val *ᵥ x = Pi.single 0 1 := by
  classical
  have hex : ∃ j : Fin (n+2), j ≠ 0 ∧ ∀ t, t ≠ 0 → t ≠ j → x t = 0 := by
    by_cases hall : ∀ t, t ≠ 0 → x t = 0
    · exact ⟨1, by simp, fun t ht _ => hall t ht⟩
    · push Not at hall
      obtain ⟨j, hj, hxj⟩ := hall
      refine ⟨j, hj, fun t _ htj => ?_⟩
      by_contra hxt
      exact htj (Finset.card_le_one.mp hs t (by simp [hxt]) j (by simp [hxj]))
  obtain ⟨j, hj, hz⟩ := hex
  have hpair : σ (x 0) * x 0 + σ (x j) * x j = 1 :=
    (norm_eq_pair σ x 0 j hj.symm hz).symm.trans hx
  obtain ⟨f, hf⟩ := exists_coordinatePlane σ hσ 0 j hj.symm
  let u := planeRotation σ hσ (x 0) (x j) hpair
  refine ⟨f u, hom_mem_twoSpaceGenerated σ hσ f u, ?_⟩
  rw [hf, planeRotation_mulVec]
  ext t
  by_cases ht : t = 0
  · subst t
    simp
  · by_cases htj : t = j
    · simp [htj, hj]
    · simp [ht, htj, hz t ht htj]

private theorem reduce_vector [Finite F] {r e : ℕ} [Fact r.Prime]
    (h2 : (2 : F) ≠ 0) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) {n : ℕ} (x : Fin (n+2) → F)
    (hx : norm σ x = 1) :
    ∃ a : (form σ hσ (n+2)).specialSubgroup,
      a ∈ twoSpaceGenerated σ hσ (n+2) ∧ a.val.val *ᵥ x = Pi.single 0 1 := by
  classical
  induction hm : (Finset.univ.filter (fun i => x i ≠ 0)).card using
      Nat.strong_induction_on generalizing x with
  | h m ih =>
    by_cases hm1 : m ≤ 1
    · exact reduce_single_support σ hσ x hx (hm ▸ hm1)
    have hs : 1 < (Finset.univ.filter (fun i => x i ≠ 0)).card := by omega
    obtain ⟨i, j, hij, hxi, hxj, hpair⟩ := exists_pair_norm_ne_zero σ h2 x hx hs
    obtain ⟨c, u, _, _, hu⟩ :=
      exists_planeRotation_of_norm_sum_ne_zero σ hσ he hc hj (x i) (x j) hpair
    obtain ⟨f, hf⟩ := exists_coordinatePlane σ hσ i j hij
    let a := f u
    let y := a.val.val *ᵥ x
    have hy (t : Fin (n+2)) : y t = if t = i then c else if t = j then 0 else x t := by
      change ((f u).val.val *ᵥ x) t = _
      rw [hf, hu]
      rfl
    have hyj : y j = 0 := by simp [hy, hij.symm]
    have hsub : Finset.univ.filter (fun t => y t ≠ 0) ⊆
        Finset.univ.filter (fun t => x t ≠ 0) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      by_cases hti : t = i
      · simpa [hti] using hxi
      by_cases htj : t = j
      · exact False.elim (ht (htj ▸ hyj))
      · simpa [hy t, hti, htj] using ht
    have hlt : (Finset.univ.filter (fun t => y t ≠ 0)).card < m := by
      rw [← hm]
      apply Finset.card_lt_card
      refine ⟨hsub, ?_⟩
      intro hh
      have hmem := hh (by simp [hxj] : j ∈ Finset.univ.filter (fun t => x t ≠ 0))
      simp [hyj] at hmem
    obtain ⟨b, hb, hby⟩ := ih _ hlt y (by simpa [y] using (norm_mulVec σ hσ a x).trans hx) rfl
    refine ⟨b*a, (twoSpaceGenerated σ hσ (n+2)).mul_mem hb
      (hom_mem_twoSpaceGenerated σ hσ f u), ?_⟩
    change (b.val.val * a.val.val) *ᵥ x = _
    rw [← Matrix.mulVec_mulVec]
    exact hby

/-- Every norm-one vector is reduced by actual embedded SU₂ factors over the same field. -/
theorem unitVectorReduction [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) (k : ℕ) : UnitVectorReduction σ hσ k := by
  have h2 : (2 : F) ≠ 0 := by
    intro h
    let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h
    let : Fintype F := Fintype.ofFinite F
    have hh := FiniteField.even_card_of_char_two (ringChar.eq F 2)
    rw [← Nat.card_eq_fintype_card, hc] at hh
    have ho : Odd ((r ^ e) ^ 2) := ((Fact.out : r.Prime).odd_of_ne_two hr).pow.pow
    exact Nat.not_even_iff_odd.mpr ho
      (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero hh))
  intro x hx
  exact reduce_vector σ hσ h2 he hc hj (n := k+1) x hx

/-- The literal SU₂ homomorphic images generate the identity-form SUₙ for all n > 0. -/
theorem twoSpaceGenerated_eq_top [Finite F] {r e : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (he : 0 < e) (hc : Nat.card F = (r ^ e) ^ 2)
    (hj : ∀ x, σ x = x ^ (r ^ e)) {n : ℕ} (hn : 0 < n) :
    twoSpaceGenerated σ hσ n = ⊤ :=
  twoSpaceGenerated_eq_top_of_reduction σ hσ (unitVectorReduction σ hσ hr he hc hj) hn
end Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
