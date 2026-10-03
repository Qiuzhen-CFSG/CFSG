module

public import ABG.Recognition.ThreeLinearThreeStructure
public import ABG.Recognition.ThreeLinearRationalCharacter
public import ABG.Recognition.ThreeLinearFixedSetGeometry
public import Theory.Character.ConjClassFunction

/-!
# Wong's local data in the order-5616 branch

The class census and Sylow-three argument give the two order-three classes,
with sizes 104 and 624. Orthogonality of the original degree-twelve character
with the principal character and with itself yields `a + 6b = 3` and
`a² + 6b² = 9`. Its integer-valuedness forces `a = 3` and `b = 0`.
Together with the previously computed even and order-thirteen values, these
are all the values in Wong's equation (14). The final package is constructed
from the original simple-group and actual involution-centralizer hypotheses.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix (b), pp.108–109, equation (14),
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

namespace ThreeGlobalDegreeData
variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)
    [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616)

include c S hS

private theorem sixth_evenRepresentative_value (i : Fin 5) :
    c.decomposition.χ 5 (c.evenRepresentative i : G) = (![4,0,1,0,0] i : ℂ) := by
  have ho := c.evenRepresentative_order i
  fin_cases i
  · exact c.sixth_value_involution S hS _ ho
  · exact c.sixth_value_order_four_or_eight S hS _ (Or.inl ho)
  · exact c.sixth_value_order_six S hS _ ho
  · exact c.sixth_value_order_four_or_eight S hS _ (Or.inr ho)
  · exact c.sixth_value_order_four_or_eight S hS _ (Or.inr ho)

include hG

private theorem sum_sixth_transform (F : ℂ → ℂ) (b : G)
    (hne : ¬ IsConj (c.linearUnipotent : G) b)
    (he : c.remainingThreeClasses =
      {ConjClasses.mk (c.linearUnipotent : G), ConjClasses.mk b})
    (hb : Nat.card (ConjClasses.mk b).carrier = 624) :
    ∑ g : G, F (c.decomposition.χ 5 g) =
      F 12 + (117 * F 4 + 702 * F 0 + 936 * F 1 + 702 * F 0 + 702 * F 0) +
      1728 * F (-1) + 104 * F (c.decomposition.χ 5 (c.linearUnipotent : G)) +
      624 * F (c.decomposition.χ 5 b) := by
  let f := toConjClassFunction (c.decomposition.χ 5)
    (irreducibleCharacter_isClassFunction (c.decomposition.irreducible 5))
  have hf (g : G) : f (ConjClasses.mk g) = c.decomposition.χ 5 g := rfl
  have hfiber (k : ConjClasses G) :
      Fintype.card {g : G // ConjClasses.mk g = k} = Nat.card k.carrier := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight
      (fun _ => ConjClasses.mem_carrier_iff_mk_eq.symm))
  have hsum : ∑ g : G, F (c.decomposition.χ 5 g) =
      ∑ k : ConjClasses G, Nat.card k.carrier • F (f k) := by
    have h := Fintype.sum_fiberwise' ConjClasses.mk (fun k => F (f k))
    simpa only [Finset.sum_const, Finset.card_univ, hfiber, hf] using h.symm
  rw [hsum, c.weighted_sum_class_census S hS hG]
  have h13 : ∑ k ∈ threeLinearThirteenClasses G, 432 • F (f k) = 1728 * F (-1) := by
    have hv (k : ConjClasses G) (hk : k ∈ threeLinearThirteenClasses G) : f k = -1 := by
      obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective k
      exact c.sixth_order_thirteen_value hG ((mem_threeLinearThirteenClasses x).mp hk)
    calc
      _ = ∑ _k ∈ threeLinearThirteenClasses G, 432 • F (-1) :=
        Finset.sum_congr rfl (fun k hk => by rw [hv k hk])
      _ = _ := by
        simp only [Finset.sum_const, c.linear_thirteen_classes_card S hS hG, nsmul_eq_mul]
        ring
  rw [h13, he, Finset.sum_pair (fun h => hne (ConjClasses.mk_eq_mk_iff_isConj.mp h)),
    c.linearUnipotent_class_card S hS hG, hb]
  simp only [c.evenClass_eq, hf, c.sixth_degree_twelve hG,
    sixth_evenRepresentative_value c S hS, nsmul_eq_mul]
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Nat.cast_ofNat]
  ring

/-- Orthogonality and integrality determine the two order-three values. -/
public theorem sixth_order_three_class_values :
    ∃ b : G, orderOf b = 3 ∧
      ¬ IsConj (c.linearUnipotent : G) b ∧
      c.remainingThreeClasses =
        {ConjClasses.mk (c.linearUnipotent : G), ConjClasses.mk b} ∧
      c.decomposition.χ 5 (c.linearUnipotent : G) = 3 ∧ c.decomposition.χ 5 b = 0 := by
  obtain ⟨b, hb, hne, he, hcard, _⟩ := c.linear_order_three_representative S hS hG
  obtain ⟨a, ha⟩ := c.sixth_value_integer hG (c.linearUnipotent : G)
  obtain ⟨d, hd⟩ := c.sixth_value_integer hG b
  have hzero : ∑ g : G, c.decomposition.χ 5 g = 0 := by
    have h := irreducibleCharacters_orthogonal (c.decomposition.irreducible 5)
      isLinearCharacter_one.1 (c.decomposition.nontrivial 5)
    simp only [characterProduct, Pi.one_apply, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by
      exact_mod_cast (Nat.card_pos (α := G)).ne'))
  have hinv (g : G) : c.decomposition.χ 5 g⁻¹ = c.decomposition.χ 5 g := by
    obtain ⟨n, ρ, _, hρ⟩ := c.decomposition.irreducible 5
    obtain ⟨z, hz⟩ := c.sixth_value_integer hG g
    rw [hρ, Representation.representation_character_inv_eq_star_character, ← hρ, hz]
    simp
  have hnorm : ∑ g : G, c.decomposition.χ 5 g * c.decomposition.χ 5 g = 5616 := by
    have h := irreducibleCharacter_self (c.decomposition.irreducible 5)
    simp only [characterProduct, hinv, hG] at h
    linear_combination 5616 * h
  have hlin := sum_sixth_transform c S hS hG (fun z => z) b hne he hcard
  have hquad := sum_sixth_transform c S hS hG (fun z => z * z) b hne he hcard
  rw [hzero, ha, hd] at hlin
  rw [hnorm, ha, hd] at hquad
  have hlin' : (a : ℂ) + 6 * (d : ℂ) = 3 := by linear_combination -hlin / 104
  have hquad' : (a : ℂ) * a + 6 * ((d : ℂ) * d) = 9 := by
    linear_combination -hquad / 104
  have hl : a + 6 * d = 3 := by exact_mod_cast hlin'
  have hq : a * a + 6 * (d * d) = 9 := by exact_mod_cast hquad'
  have hd0 : d = 0 := by
    have h : d * (7 * d - 6) = 0 := by nlinarith [sq_nonneg (a + 6 * d - 3)]
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · omega
  have ha3 : a = 3 := by omega
  exact ⟨b, hb, hne, he, by simpa [ha3] using ha, by simpa [hd0] using hd⟩

/-- Equation (14) on elements of order three, distinguished by their centralizers. -/
public theorem sixth_value_order_three (x : G) (hx : orderOf x = 3) :
    c.decomposition.χ 5 x =
      if Nat.card (Subgroup.centralizer ({x} : Set G)) = 54 then 3 else 0 := by
  obtain ⟨b, _, hne, he, hu, hb⟩ := c.sixth_order_three_class_values S hS hG
  let f := toConjClassFunction (c.decomposition.χ 5)
    (irreducibleCharacter_isClassFunction (c.decomposition.irreducible 5))
  have hf {y z : G} (h : ConjClasses.mk y = ConjClasses.mk z) :
      c.decomposition.χ 5 y = c.decomposition.χ 5 z := congrArg f h
  have hm := (c.mk_mem_remainingThreeClasses_iff_order S hS hG x).mpr (Or.inl hx)
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  by_cases hc : Nat.card (Subgroup.centralizer ({x} : Set G)) = 54
  · rw [if_pos hc]
    exact (hf (ConjClasses.mk_eq_mk_iff_isConj.mpr
      ((c.linear_isConj_unipotent_iff S hS hG x (Or.inl hx)).mpr hc))).symm.trans hu
  · rw [if_neg hc]
    rcases hm with hm | hm
    · exact False.elim (hc ((c.linear_isConj_unipotent_iff S hS hG x (Or.inl hx)).mp
        (ConjClasses.mk_eq_mk_iff_isConj.mp hm.symm)))
    · exact (hf hm).trans hb

/-- The elements eligible to define Wong's points are exactly the unipotent class. -/
public theorem linear_isPointElement_iff (x : G) :
    ThreeLinearPlane.IsPointElement G x ↔ IsConj (c.linearUnipotent : G) x := by
  constructor
  · intro hx
    exact (c.linear_isConj_unipotent_iff S hS hG x (Or.inl hx.1)).mpr hx.2
  · intro hx
    have ho : orderOf x = 3 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq _).trans c.linearUnipotent_order
    exact ⟨ho, (c.linear_isConj_unipotent_iff S hS hG x (Or.inl ho)).mp hx⟩

/-- There are exactly 104 eligible elements, with no choice of a class label. -/
public theorem linear_pointElement_card :
    Nat.card {x : G // ThreeLinearPlane.IsPointElement G x} = 104 := by
  calc
    _ = Nat.card (ConjClasses.mk (c.linearUnipotent : G)).carrier :=
      Nat.card_congr (Equiv.subtypeEquivRight (c.linear_isPointElement_iff S hS hG))
    _ = 104 := c.linearUnipotent_class_card S hS hG

/-- All values of the original degree-twelve character in Wong's equation (14). -/
public theorem sixth_linear_values (x : G) :
    c.decomposition.χ 5 x =
      if x = 1 then 12 else if orderOf x = 2 then 4 else
      if ThreeLinearPlane.IsPointElement G x then 3 else
      if orderOf x = 6 then 1 else if orderOf x = 13 then -1 else 0 := by
  by_cases h1 : x = 1
  · simpa [h1] using c.sixth_degree_twelve hG
  simp only [if_neg h1]
  have ho := c.linear_element_order_coverage S hS hG x
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with ho | ho | ho | ho | ho | ho | ho
  · exact False.elim (h1 (orderOf_eq_one_iff.mp ho))
  · simp [ho, c.sixth_value_involution S hS x ho]
  · simpa [ho, ThreeLinearPlane.IsPointElement] using c.sixth_value_order_three S hS hG x ho
  · simp [ho, ThreeLinearPlane.IsPointElement,
      c.sixth_value_order_four_or_eight S hS x (Or.inl ho)]
  · simp [ho, ThreeLinearPlane.IsPointElement, c.sixth_value_order_six S hS x ho]
  · simp [ho, ThreeLinearPlane.IsPointElement,
      c.sixth_value_order_four_or_eight S hS x (Or.inr ho)]
  · simp [ho, ThreeLinearPlane.IsPointElement, c.sixth_order_thirteen_value hG ho]

end ThreeGlobalDegreeData

/-- The local data and equation (14), retaining the original catalog and its
actual degree-twelve representation. All fields are derived below. -/
public structure ThreeLinearLocalData (G : Type*) [Group G] [Finite G]
    extends ThreeLinearCharacterData G where
  three_class_census : ∃ b : G, orderOf b = 3 ∧
    ¬ IsConj (toThreeGlobalDegreeData.linearUnipotent : G) b ∧
    ConjClasses.ofOrder G 3 =
      {ConjClasses.mk (toThreeGlobalDegreeData.linearUnipotent : G), ConjClasses.mk b} ∧
    Nat.card (ConjClasses.mk (toThreeGlobalDegreeData.linearUnipotent : G)).carrier = 104 ∧
    Nat.card (Subgroup.centralizer ({(toThreeGlobalDegreeData.linearUnipotent : G)} : Set G)) = 54 ∧
    Nat.card (ConjClasses.mk b).carrier = 624 ∧
    Nat.card (Subgroup.centralizer ({b} : Set G)) = 9
  eligible_card : Nat.card {x : G // ThreeLinearPlane.IsPointElement G x} = 104
  sylow_three_card : ∀ P : Sylow 3 G, Nat.card P = 27
  sylow_three_exponent : ∀ P : Sylow 3 G, Monoid.exponent P = 3
  sylow_three_nonabelian : ∀ P : Sylow 3 G, ¬ IsMulCommutative P
  element_orders : ∀ x : G, orderOf x ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ)
  sixth_values : ∀ x : G, decomposition.χ 5 x =
    if x = 1 then 12 else if orderOf x = 2 then 4 else
    if ThreeLinearPlane.IsPointElement G x then 3 else
    if orderOf x = 6 then 1 else if orderOf x = 13 then -1 else 0

/-- Assemble the local conclusions without replacing the supplied character catalog. -/
public theorem ThreeLinearCharacterData.exists_localData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (c : ThreeLinearCharacterData G)
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) :
    ∃ d : ThreeLinearLocalData G, d.toThreeLinearCharacterData = c := by
  exact ⟨{
    toThreeLinearCharacterData := c
    three_class_census := c.toThreeGlobalDegreeData.linear_order_three_class_census S hS c.group_order
    eligible_card := c.toThreeGlobalDegreeData.linear_pointElement_card S hS c.group_order
    sylow_three_card := threeLinear_sylow_three_card c.group_order
    sylow_three_exponent := c.toThreeGlobalDegreeData.linear_sylow_three_exponent S hS c.group_order
    sylow_three_nonabelian := c.toThreeGlobalDegreeData.linear_sylow_three_nonabelian S hS c.group_order
    element_orders := c.toThreeGlobalDegreeData.linear_element_order_coverage S hS c.group_order
    sixth_values := c.toThreeGlobalDegreeData.sixth_linear_values S hS c.group_order }, rfl⟩

/-- Wong's local data follow from the original hypotheses, including actual
GL₂(3) equivalences rather than assumed centralizer tables. -/
public theorem exists_threeLinearLocalData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) : Nonempty (ThreeLinearLocalData G) := by
  obtain ⟨c⟩ := exists_threeLinearCharacterData S hS hcard hC hG
  obtain ⟨d, _⟩ := c.exists_localData S hS
  exact ⟨d⟩

end
end ABG
