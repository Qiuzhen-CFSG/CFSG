module
public import ABG.Recognition.ThreeMathieuEvenCharacterValues
public import ABG.Recognition.ThreeMathieuOddClasses
public import Theory.Character.UniqueDegreeRationality
public import Theory.Character.FiniteOrderTrace
public import Theory.Character.ColumnBound
public import Theory.Character.ClassFunctionSum

/-!
# The first character on Wong's odd-order classes

Galois conjugation preserves degree and involution value; these distinguish the
first member of the shared catalog. Its values are therefore integers. The
prime-order trace congruence and column bound determine the values at five and
eleven. Orthogonality with the trivial character then gives the value at three.

Source: Wong (1964), Theorem 6(a), p.107,
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators
noncomputable section

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)

include S hS in
/-- Galois conjugation fixes the first character, distinguished by its degree
and its value two at the involution. -/
public theorem ThreeGlobalDegreeData.first_character_galois_fixed
    (hG : Nat.card G = 7920) (σ : ℂ ≃+* ℂ) (x : G) :
    σ (c.decomposition.χ 0 x) = c.decomposition.χ 0 x := by
  have hχ := (c.decomposition.irreducible 0).comp_ringEquiv σ
  have hd : σ (c.decomposition.χ 0 1) = 10 := by
    rw [c.first_character_identity hG]
    exact map_ofNat σ 10
  have ht (i : Fin 7) := threeInduced_involution_vector S hS c.involution
    c.order_involution c.centralizerEquiv c.decomposition i
  rcases (c.mathieu_degree_ten_iff hG hχ).mp hd with h | h | h
  · exact congrFun h x
  · have he := congrFun h c.involution
    simp only [ht] at he
    change σ (2 : ℂ) = -2 at he
    norm_num only [map_ofNat] at he
  · have he := congrFun h c.involution
    simp only [ht] at he
    change σ (2 : ℂ) = -2 at he
    norm_num only [map_ofNat] at he

include S hS in
/-- All values of the first character are integers. -/
public theorem ThreeGlobalDegreeData.first_character_integer
    (hG : Nat.card G = 7920) (x : G) :
    ∃ a : ℤ, c.decomposition.χ 0 x = (a : ℂ) :=
  (c.decomposition.irreducible 0).integer_of_fixed
    (c.first_character_galois_fixed S hS hG) x

omit [IsSimpleGroup G] in
private theorem first_prime_congruence (hG : Nat.card G = 7920)
    (x : G) {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    (a : ℤ) (ha : c.decomposition.χ 0 x = (a : ℂ)) :
    (p : ℤ) ∣ a - 10 := by
  obtain ⟨n, ρ, _, hχ⟩ := c.decomposition.irreducible 0
  have hn : n = 10 := by
    have hd := c.first_character_identity hG
    rw [hχ, Representation.char_one] at hd
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      (show Module.finrank ℂ (Fin n → ℂ) = 10 by exact_mod_cast hd)
  have hpow : (ρ x) ^ p = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have h := prime_dvd_integer_trace_sub_finrank (ρ x) hp hpow a (by simpa [hχ, Representation.character] using ha)
  simpa [hn] using h

include S hS in
/-- The first character vanishes on the unique order-five class. -/
public theorem ThreeGlobalDegreeData.first_character_order_five
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 5) :
    c.decomposition.χ 0 x = 0 := by
  obtain ⟨a, ha⟩ := c.first_character_integer S hS hG x
  have hb := (c.decomposition.irreducible 0).normSq_le_centralizer_card x
  rw [c.mathieu_five_centralizer_card S hS hG x hx, ha] at hb
  have hb' : a * a ≤ 5 := by
    exact_mod_cast (show (a : ℝ) * a ≤ 5 by simpa [Complex.normSq_apply] using hb)
  obtain ⟨k, hk⟩ := first_prime_congruence c hG x (by decide) hx a ha
  have hlo : -2 ≤ a := by nlinarith
  have hhi : a ≤ 2 := by nlinarith
  have ha0 : a = 0 := by omega
  simpa [ha0] using ha

include S hS in
/-- The first character is minus one on both order-eleven classes. -/
public theorem ThreeGlobalDegreeData.first_character_order_eleven
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 11) :
    c.decomposition.χ 0 x = -1 := by
  obtain ⟨a, ha⟩ := c.first_character_integer S hS hG x
  have hb := (c.decomposition.irreducible 0).normSq_le_centralizer_card x
  rw [c.mathieu_eleven_centralizer_card S hS hG x hx, ha] at hb
  have hb' : a * a ≤ 11 := by
    exact_mod_cast (show (a : ℝ) * a ≤ 11 by simpa [Complex.normSq_apply] using hb)
  obtain ⟨k, hk⟩ := first_prime_congruence c hG x (by decide) hx a ha
  have hlo : -3 ≤ a := by nlinarith
  have hhi : a ≤ 3 := by nlinarith
  have ha1 : a = -1 := by omega
  simpa [ha1] using ha

include S hS in
/-- Orthogonality with the trivial character gives value one on the order-three class. -/
public theorem ThreeGlobalDegreeData.first_character_order_three
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 3) :
    c.decomposition.χ 0 x = 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨a, b, z, ha, hb, hz, hr⟩ := c.exists_mathieu_class_representatives S hS hG
  let r : Fin 10 → G := ![1, (c.evenRepresentative 0 : G), (c.evenRepresentative 1 : G),
    (c.evenRepresentative 2 : G), (c.evenRepresentative 3 : G),
    (c.evenRepresentative 4 : G), a, b, z, z⁻¹]
  have hzero : ∑ g : G, c.decomposition.χ 0 g = 0 := by
    have h := irreducibleCharacters_orthogonal (c.decomposition.irreducible 0)
      isLinearCharacter_one.1 (c.decomposition.nontrivial 0)
    simp only [characterProduct, Pi.one_apply, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by
      exact_mod_cast (Nat.card_pos (α := G)).ne'))
  have hsum := (irreducibleCharacter_isClassFunction (c.decomposition.irreducible 0)).sum_eq_sum_class_representatives r hr
  rw [hzero] at hsum
  have hsize (y : G) (n : ℕ) (hn : Nat.card (Subgroup.centralizer ({y} : Set G)) = n)
      (hne : n ≠ 0) : Nat.card (ConjClasses.mk y).carrier = 7920 / n := by
    apply Nat.eq_div_of_mul_eq_left hne
    have he : Nat.card {g : G // g * y = y * g} =
        Nat.card (Subgroup.centralizer ({y} : Set G)) := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun _ => Subgroup.mem_centralizer_singleton_iff.symm)
    rw [← hn, ← he, class_card_mul_centralizer_card, hG]
  have hone : Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
    have he : (ConjClasses.mk (1 : G)).carrier = {1} := by
      ext y
      change IsConj 1 y ↔ y = 1
      exact isConj_one_right
    rw [he]
    simp
  have heven (i : Fin 5) : Nat.card (ConjClasses.mk (c.evenRepresentative i : G)).carrier =
      ![165,990,1320,990,990] i := by
    rw [hsize _ _ (c.evenRepresentative_centralizer_card i) (by fin_cases i <;> decide)]
    fin_cases i <;> rfl
  have hasize := hsize a 18 (c.mathieu_three_centralizer_card S hS hG a ha) (by decide)
  have hbsize := hsize b 5 (c.mathieu_five_centralizer_card S hS hG b hb) (by decide)
  have hzsize := hsize z 11 (c.mathieu_eleven_centralizer_card S hS hG z hz) (by decide)
  have hzisize := hsize z⁻¹ 11 (c.mathieu_eleven_centralizer_card S hS hG z⁻¹
    (by simpa using hz)) (by decide)
  simp only [r, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at hsum
  rw [hone, heven 0, heven 1, heven 2, heven 3, heven 4, hasize, hbsize, hzsize, hzisize,
    c.first_character_identity hG, c.first_evenRepresentative_value,
    c.first_evenRepresentative_value, c.first_evenRepresentative_value,
    c.first_evenRepresentative_value, c.first_evenRepresentative_value,
    c.first_character_order_five S hS hG b hb,
    c.first_character_order_eleven S hS hG z hz,
    c.first_character_order_eleven S hS hG z⁻¹ (by simpa using hz)] at hsum
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons] at hsum
  have haval : c.decomposition.χ 0 a = 1 := by linear_combination -hsum / 440
  obtain ⟨i, hi⟩ := hr.surjective (ConjClasses.mk x)
  have hconj := ConjClasses.mk_eq_mk_iff_isConj.mp hi
  have ho : orderOf (r i) = orderOf x := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact (MulAut.conj g).orderOf_eq _ |>.symm
  rw [hx] at ho
  fin_cases i <;> simp [r, c.evenRepresentative_order, ha, hb, hz] at ho
  exact (c.first_character_conjugacy_invariant hconj).symm.trans haval

end
end ABG
