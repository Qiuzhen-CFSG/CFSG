module

public import Theory.GroupAction.C4SquareActionDichotomySetup

/-!
# Encoding nested automorphism subgroups of the C₄-square

For nested subgroups `H ≤ K` of orders four and eight, with `H` consisting
of the elements of `K` fixing every involution, choose two nonidentity
elements of `H` and encode them by binary congruence matrices.
Their four distinct words exhaust `H`. An element of `K` outside `H` has
square in `H` by index two, and conjugates `H` into itself because fixing
all involutions is invariant under conjugation. Its columns therefore
satisfy the finite `Valid` contract.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace C4SquareExtension.ActionDichotomy

private theorem encoding_word_injective {m n : Code}
    (hm : m ≠ zeroCode) (hn : n ≠ zeroCode) (hmn : m ≠ n) :
    Function.Injective (word m n) := by
  have hu : congruenceAut m ≠ 1 := by
    intro h
    exact hm (congruenceAut_injective (h.trans congruenceAut_zero.symm))
  have hv : congruenceAut n ≠ 1 := by
    intro h
    exact hn (congruenceAut_injective (h.trans congruenceAut_zero.symm))
  have huv : congruenceAut m ≠ congruenceAut n := fun h => hmn (congruenceAut_injective h)
  have huu : congruenceAut m * congruenceAut m = 1 := by
    apply MulEquiv.ext
    exact congruenceAct_involutive m
  have huv1 : congruenceAut m * congruenceAut n ≠ 1 := by
    intro h
    exact huv (mul_left_cancel (h.trans huu.symm)).symm
  have huv_u : congruenceAut m * congruenceAut n ≠ congruenceAut m := by
    intro h
    exact hv (mul_left_cancel (h.trans (mul_one _).symm))
  have huv_v : congruenceAut m * congruenceAut n ≠ congruenceAut n := by
    intro h
    exact hu (mul_right_cancel (h.trans (one_mul _).symm))
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [word] at hij ⊢
  all_goals first
    | exact (hu hij).elim
    | exact (hu hij.symm).elim
    | exact (hv hij).elim
    | exact (hv hij.symm).elim
    | exact (huv hij).elim
    | exact (huv hij.symm).elim
    | exact (huv1 hij).elim
    | exact (huv1 hij.symm).elim
    | exact (huv_u hij).elim
    | exact (huv_u hij.symm).elim
    | exact (huv_v hij).elim
    | exact (huv_v hij.symm).elim

private theorem encoding_two_elements (H : Subgroup (MulAut Model))
    (hH : Nat.card H = 4) :
    ∃ u ∈ H, ∃ v ∈ H, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  let : Finite H := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype H := Fintype.ofFinite H
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : H)
  have hsmall : ({1, u} : Finset H).card < (Finset.univ : Finset H).card := by
    have := Finset.card_le_two (a := (1 : H)) (b := u)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact ⟨u, u.property, v, v.property,
    fun h => hu (Subtype.ext h), fun h => hv.1 (Subtype.ext h),
    fun h => hv.2 (Subtype.ext h.symm)⟩

private theorem encoding_goodBasis (t : MulAut Model) : GoodBasis (t e₁) (t e₂) := by
  have hb : GoodBasis e₁ e₂ := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hb.1
    apply t.injective
    simpa only [map_pow, map_one] using h
  · intro h
    apply hb.2.1
    apply t.injective
    simpa only [map_pow, map_one] using h
  · intro h
    apply hb.2.2
    apply t.injective
    simpa only [map_pow] using h

/-- Extract a finite coordinate input from the nested automorphism subgroups,
retaining the memberships needed to reconstruct the action frames. -/
public theorem exists_encodedActionPair (H K : Subgroup (MulAut Model))
    (hHK : H ≤ K) (hH : Nat.card H = 4) (hK : Nat.card K = 8)
    (hfix : ∀ α ∈ K, α ∈ H ↔ ∀ a : Model, a ^ 2 = 1 → α a = a)
    (hinv : ∀ α ∈ H, α ≠ 1 → ∃ a : Model, α a = a⁻¹ ∧ a ^ 2 ≠ 1) :
    Nonempty (EncodedActionPair H K) := by
  classical
  obtain ⟨u, huH, v, hvH, hu, hv, huv⟩ := encoding_two_elements H hH
  obtain ⟨m, rfl⟩ := exists_congruenceAut u ((hfix u (hHK huH)).mp huH)
  obtain ⟨n, rfl⟩ := exists_congruenceAut v ((hfix v (hHK hvH)).mp hvH)
  have hm : m ≠ zeroCode := by
    rintro rfl
    exact hu congruenceAut_zero
  have hn : n ≠ zeroCode := by
    rintro rfl
    exact hv congruenceAut_zero
  have hmn : m ≠ n := fun h => huv (congrArg congruenceAut h)
  have hmem (i : Fin 4) : word m n i ∈ H := by
    fin_cases i
    · exact H.one_mem
    · exact huH
    · exact hvH
    · exact H.mul_mem huH hvH
  have hwi := encoding_word_injective hm hn hmn
  have hexhaust (a : MulAut Model) (ha : a ∈ H) : ∃ i, word m n i = a := by
    let f : Fin 4 → H := fun i => ⟨word m n i, hmem i⟩
    have hf : Function.Injective f := fun i j h => hwi (congrArg Subtype.val h)
    have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hf, by simpa using hH.symm⟩).2
    obtain ⟨i, hi⟩ := hsurj ⟨a, ha⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hcard : Nat.card (H.subgroupOf K) = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv).trans hH
  have hindex : (H.subgroupOf K).index = 2 := by
    have h := (H.subgroupOf K).card_mul_index
    rw [hcard, hK] at h
    omega
  obtain ⟨t, htK, htH, _⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hindex)
  have ht2 : t * t ∈ H :=
    (H.subgroupOf K).mul_self_mem_of_index_two hindex ⟨t, htK⟩
  have hconj (a : MulAut Model) (ha : a ∈ H) : t * a * t⁻¹ ∈ H := by
    apply (hfix _ (K.mul_mem (K.mul_mem htK (hHK ha)) (K.inv_mem htK))).mpr
    intro x hx
    have hy : (t⁻¹ x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    change t (a (t⁻¹ x)) = x
    rw [(hfix a (hHK ha)).mp ha _ hy]
    exact t.apply_symm_apply x
  refine ⟨{
    m := m, n := n, t := t, words_mem := hmem, t_mem := htK
    valid := ⟨hm, hn, hmn, ?_, encoding_goodBasis t, ?_, ?_, ?_⟩ }⟩
  · intro i hi
    apply hinv _ (hmem i)
    intro heq
    apply hi
    apply hwi
    simpa [word] using heq
  · by_contra h
    apply htH
    apply (hfix t htK).mpr
    intro a ha
    by_contra hne
    exact h ⟨a, ha, by simpa only [← aut_eq_outerAct] using hne⟩
  · obtain ⟨i, hi⟩ := hexhaust (t * t) ht2
    refine ⟨i, fun x => ?_⟩
    simp only [← aut_eq_outerAct]
    exact (congrArg (fun f : MulAut Model => f x) hi).symm
  · intro i
    obtain ⟨j, hj⟩ := hexhaust _ (hconj _ (hmem i))
    refine ⟨j, fun x => ?_⟩
    simp only [← aut_eq_outerAct]
    rw [hj]
    change t (word m n i x) = t (word m n i (t⁻¹ (t x)))
    rw [show t⁻¹ (t x) = x from t.symm_apply_apply x]

end C4SquareExtension.ActionDichotomy
