module
public import ABG.Recognition.ThreeLinearCharacters
public import ABG.Recognition.ThreeCharacterDegreeInventory

/-!+# Even-order data for Wong's linear branch

Involution fusion carries every even-order element into the cyclic roots of
the distinguished involution. The actual GL₂(3) conjugacy table then gives
five representatives, of orders 2, 4, 6, 8, 8. Restricting the original sixth
character to these roots gives values 4, 0, 1, 0, 0. The results retain the
shared catalog and apply to its actual degree-twelve representation.

The group order also gives Sylow subgroup orders 27 and 13. This is the
even-order part of Wong (1964), Appendix (b), pp.108–109, equation (14),
DOI 10.1017/S1446788700022771. The odd-order class census is a separate step.
-/

namespace ABG
open BenderGlauberman Matrix.GeneralLinearGroup
noncomputable section

variable {G : Type*} [Group G] [Finite G]

private theorem involution_fusion [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (t : G) (ht : orderOf t = 2) (u : G) (hu : orderOf u = 2) : IsConj u t := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hi⟩ := hcov u hu
  obtain ⟨j, hj⟩ := hcov t ht
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

/-- Every even-order element is conjugate to one of the five transported
root representatives in the supplied involution centralizer. -/
public theorem threeCentralizer_even_class_representative [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (x : G) (hx : 2 ∣ orderOf x) :
    ∃ j : Fin 8, (j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7) ∧
      IsConj x (((threeCentralizerEquiv t e).symm (threeClassRepr j)) : G) := by
  obtain ⟨a, ha, hxa⟩ := exists_isConj_involution_root_of_even t
    (involution_fusion S hS t ht) x hx
  obtain ⟨j, hj, _⟩ := three_conjugacy_data.1 (threeCentralizerEquiv t e a)
  have hr := (threeCentralizerEquiv_root_iff t ht e a).mpr ha
  have hrj := (threeCentral_mem_zpowers_isConj hj).mp hr
  have hj' : IsConj a ((threeCentralizerEquiv t e).symm (threeClassRepr j)) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      (threeCentralizerEquiv t e).symm.toMonoidHom.map_isConj hj
  exact ⟨j, (three_conjugacy_data.2.2.2 j).mp hrj,
    hxa.trans ((Subgroup.centralizer ({t} : Set G)).subtype.map_isConj hj')⟩

omit [Finite G] in
/-- The supplied table representative has the same order in the ambient group. -/
public theorem threeCentralizer_class_representative_order
    (t : G) (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) (j : Fin 8) :
    orderOf (((threeCentralizerEquiv t e).symm (threeClassRepr j)) : G) =
      ![1,2,4,3,6,2,8,8] j := by
  rw [Subgroup.orderOf_coe,
    (threeCentralizerEquiv t e).symm.orderOf_eq,
    three_conjugacy_data.2.1]

namespace ThreeGlobalDegreeData

variable (c : ThreeGlobalDegreeData G)

/-- The sixth character's values on the five roots, with the sign resolved. -/
public theorem sixth_root_values (j : Fin 8)
    (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 7) :
    c.decomposition.χ 5
      ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm (threeClassRepr j)) =
        (![0,4,0,0,1,0,0,0] j : ℂ) := by
  have ha := (threeCentralizerEquiv_root_iff c.involution c.order_involution
    c.centralizerEquiv
    ((threeCentralizerEquiv c.involution c.centralizerEquiv).symm (threeClassRepr j))).mp
      (by simpa only [MulEquiv.apply_symm_apply, glTwoThreeRootSupport_class] using hj)
  rw [c.sixth_restriction _ ha, threeCentralizerCharacter_values]
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · change -(-4 : ℂ) = 4; norm_num
  · change -(0 : ℂ) = 0; norm_num
  · change -(-1 : ℂ) = 1; norm_num
  · change -(0 : ℂ) = 0; norm_num
  · change -(0 : ℂ) = 0; norm_num

/-- The possible even orders and the corresponding values of the original χ₆. -/
public theorem sixth_even_order_values [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : 2 ∣ orderOf x) :
    (orderOf x = 2 ∧ c.decomposition.χ 5 x = 4) ∨
    (orderOf x = 4 ∧ c.decomposition.χ 5 x = 0) ∨
    (orderOf x = 6 ∧ c.decomposition.χ 5 x = 1) ∨
    (orderOf x = 8 ∧ c.decomposition.χ 5 x = 0) := by
  obtain ⟨j, hj, hconj⟩ := threeCentralizer_even_class_representative S hS
    c.involution c.order_involution c.centralizerEquiv x hx
  have ho : orderOf x = ![1,2,4,3,6,2,8,8] j := by
    rw [← threeCentralizer_class_representative_order c.involution c.centralizerEquiv j]
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).symm
  have hv : c.decomposition.χ 5 x = (![0,4,0,0,1,0,0,0] j : ℂ) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← c.sixth_root_values j hj, ← hg]
    exact (irreducibleCharacter_isClassFunction (c.decomposition.irreducible 5) x g).symm
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨ho, hv⟩
  · exact Or.inr (Or.inl ⟨ho, hv⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ho, hv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hv⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hv⟩))

/-- χ₆ has value four at every involution. -/
public theorem sixth_value_involution [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) : c.decomposition.χ 5 x = 4 := by
  rcases c.sixth_even_order_values S hS x (by omega) with h | h | h | h
  · exact h.2
  all_goals omega

/-- χ₆ has value one at every element of order six. -/
public theorem sixth_value_order_six [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 6) : c.decomposition.χ 5 x = 1 := by
  rcases c.sixth_even_order_values S hS x (by omega) with h | h | h | h
  · omega
  · omega
  · exact h.2
  · omega

/-- χ₆ vanishes at elements of order four or eight. -/
public theorem sixth_value_order_four_or_eight [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 4 ∨ orderOf x = 8) : c.decomposition.χ 5 x = 0 := by
  rcases c.sixth_even_order_values S hS x (by omega) with h | h | h | h
  · omega
  · exact h.2
  · omega
  · exact h.2

end ThreeGlobalDegreeData

/-- The 3-part of the order 5616 is 27. -/
public theorem threeLinear_sylow_three_card (hG : Nat.card G = 5616)
    (P : Sylow 3 G) : Nat.card P = 27 := by
  rw [P.card_eq_multiplicity, hG]
  rw [show (5616 : ℕ) = 2^4 * 3^3 * 13 from rfl,
    Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_pow, Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization,
    (show Nat.Prime 13 by decide).factorization]

/-- The 13-part of the order 5616 is 13. -/
public theorem threeLinear_sylow_thirteen_card (hG : Nat.card G = 5616)
    (P : Sylow 13 G) : Nat.card P = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [P.card_eq_multiplicity, hG]
  rw [show (5616 : ℕ) = 2^4 * 3^3 * 13 from rfl,
    Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_pow, Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization,
    (show Nat.Prime 13 by decide).factorization]

end
end ABG
