module
public import ABG.Recognition.ThreeQuotientSectionAssembly
public import Stellmacher.Recognition.SemidihedralCentralizerQuotient
public import Theory.Character.IntegralRestriction
public import ABG.ChapterII.Section1.SixteenSum

/-!
# The two signed principal-degree congruences

For the actual quotient-induced catalog, restriction to the semidihedral
Sylow subgroup gives the two degree congruences modulo sixteen. Every
involution is conjugate to the distinguished involution. An element of
order four or eight is therefore conjugate to a cyclic root of that
involution, where the existing root-restriction formula applies through
the actual odd-core quotient. The order census evaluates the Sylow sums;
ordinary character multiplicity makes those sums divisible by sixteen.
The odd core and all character signs remain unresolved.

Source: Alperin--Brauer--Gorenstein III.6 Corollary 6, using the local
character table and II.1--2 involution fusion.
-/

open scoped BigOperators
namespace Stellmacher.Recognition
open ABG BenderGlauberman ModularBlock.PrincipalBlockConstruction Matrix.GeneralLinearGroup
noncomputable section
attribute [local instance] Fintype.ofFinite
private theorem class_eq {H : Type*} [Group H] {f : H → ℂ}
    (hf : IsClassFunction f) {a b : H} (h : IsConj a b) : f a = f b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (hf a g).symm

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2)
local notation "C" => Subgroup.centralizer (Set.singleton x)

include S hS hx in
private theorem involution_conjugate (y : G) (hy : orderOf y = 2) : IsConj y x := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨_, _, _, hcov⟩ := hclass
  obtain ⟨i, hi⟩ := hcov y hy
  obtain ⟨j, hj⟩ := hcov x hx
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

include S hS hx in
private theorem root_conjugate (y : G) (hy : orderOf y = 4 ∨ orderOf y = 8) :
    ∃ a : C, IsConj y (a : G) ∧ x ∈ Subgroup.zpowers (a : G) := by
  have hz : orderOf (y ^ (orderOf y / 2)) = 2 := by
    rw [orderOf_pow]
    rcases hy with h | h <;> rw [h] <;> norm_num
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_conjugate S hS x hx _ hz)
  let f := MulAut.conj g
  have hp : (f y) ^ (orderOf y / 2) = x := by
    rw [← map_pow]
    exact hg
  have hm : f y ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← hp]
    exact (Commute.refl (f y)).pow_right _
  exact ⟨⟨f y, hm⟩, isConj_iff.mpr ⟨g, rfl⟩,
    ⟨((orderOf y / 2 : ℕ) : ℤ), by simpa only [zpow_natCast] using hp⟩⟩

omit [IsSimpleGroup G] in
private theorem quotient_order
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (a : C) (ha : orderOf a = 4 ∨ orderOf a = 8) :
    orderOf (threeOddCoreQuotientMap e a) = orderOf a := by
  have hk : (threeOddCoreQuotientMap e).ker = pPrimeCore 2 C := by
    rw [threeOddCoreQuotientMap,
      MonoidHom.ker_comp_of_injective _ _ (e.trans glTwoThreeFieldEquiv).injective,
      QuotientGroup.ker_mk']
  apply MonoidHom.orderOf_eq_of_prime_power_of_coprime_ker
    (p := 2) (threeOddCoreQuotientMap e) (by rw [hk]; exact pPrimeCore_coprime_card)
  rcases ha with ha | ha
  · exact ⟨2, by simpa only [show 2^2 = 4 from rfl, ← ha] using pow_orderOf_eq_one a⟩
  · exact ⟨3, by simpa only [show 2^3 = 8 from rfl, ← ha] using pow_orderOf_eq_one a⟩

private theorem table_values (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (ha : orderOf a = 4 ∨ orderOf a = 8) :
    glTwoThreeCharacter 4 a = -1 ∧
      glTwoThreeCharacter 3 a = if orderOf a = 4 then -1 else 1 := by
  obtain ⟨k, hk, _⟩ := three_conjugacy_data.1 a
  have ho : orderOf a = (![1,2,4,3,6,2,8,8] k : ℕ) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hk
    rw [← three_conjugacy_data.2.1 k, ← hg]
    exact ((MulAut.conj g).orderOf_eq a).symm
  rw [class_eq (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible 4)) hk,
    class_eq (irreducibleCharacter_isClassFunction (glTwoThreeCharacter_irreducible 3)) hk,
    glTwoThreeCharacter_values, glTwoThreeCharacter_values, ho]
  rw [ho] at ha
  fin_cases k <;> simp_all [glTwoThreeCharacterTable, Matrix.cons_val, Fin.reduceFinMk]

include S hS hx in
/-- The actual candidate rows on all involutions of the ambient simple group. -/
public theorem threeQuotient_principalCandidate_all_involutions
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (y : G) (hy : orderOf y = 2) :
    d.principalCandidate 1 y = (3 * d.sign 0 : ℤ) ∧
      d.principalCandidate 2 y = (-3 * d.sign 3 : ℤ) := by
  obtain ⟨b⟩ := exists_principalCongruenceBlockData G
  have he (i : Fin 8) := class_eq
    (irreducibleCharacter_isClassFunction (d.principalCandidate_irreducible i))
    (involution_conjugate S hS x hx y hy)
  constructor
  · rw [he, threeQuotient_principalCandidate_involution x e d b hx]
    rfl
  · rw [he, threeQuotient_principalCandidate_involution x e d b hx]
    rfl

include S hS hx in
/-- Root restriction determines both relevant rows on every element of order
four or eight. The odd core is retained throughout. -/
public theorem threeQuotient_principalCandidate_all_four_eight
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (y : G) (hy : orderOf y = 4 ∨ orderOf y = 8) :
    d.principalCandidate 1 y = (-d.sign 0 : ℤ) ∧
      d.principalCandidate 2 y =
        (if orderOf y = 4 then d.sign 3 else -d.sign 3 : ℤ) := by
  obtain ⟨b⟩ := exists_principalCongruenceBlockData G
  obtain ⟨a, hya, hxa⟩ := root_conjugate S hS x hx y hy
  have hao : orderOf a = orderOf y := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hya
    rw [← Subgroup.orderOf_coe, ← hg]
    exact (MulAut.conj g).orderOf_eq y
  have hqa : orderOf (threeOddCoreQuotientMap e a) = orderOf y :=
    (quotient_order x e a (hao.symm ▸ hy)).trans hao
  have hv := table_values (threeOddCoreQuotientMap e a) (hqa.symm ▸ hy)
  have he (i : Fin 8) := (class_eq
    (irreducibleCharacter_isClassFunction (d.principalCandidate_irreducible i)) hya).trans
    (threeQuotient_principalCandidate_root_restriction x e d b hx a hxa i)
  constructor
  · rw [he 1]
    change (d.sign 0 : ℤ) * glTwoThreeCharacter 4 _ = _
    rw [hv.1]
    simp
  · rw [he 2]
    change (-d.sign 3 : ℤ) * glTwoThreeCharacter 3 _ = _
    rw [hv.2, hqa]
    split_ifs <;> simp

include S hS hx in
/-- The signed degree congruences for the actual catalog, before resolving
signs or eliminating the local odd core. -/
public theorem threeQuotient_principalCandidate_signed_degree_congruences
    (hN : Stellmacher.IsNTwoGroup G)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e)) :
    (16 ∣ -d.sign 0 * (d.principalSectionDegree 0 : ℤ) - 5) ∧
      (16 ∣ -d.sign 3 * (d.principalSectionDegree 1 : ℤ) - 3) := by
  have hc := semidihedral_sylow_card_sixteen_of_simple_nTwo S hS hN
  have hχ (i : Fin 8) : IsCharacter (d.principalCandidate i) := by
    obtain ⟨n, ρ, _, hρ⟩ := d.principalCandidate_irreducible i
    exact ⟨n, ρ, hρ⟩
  have h₂ (y : S) (hy : orderOf y = 2) :=
    threeQuotient_principalCandidate_all_involutions S hS x hx e d y
      ((Subgroup.orderOf_coe y).trans hy)
  have h₄₈ (y : S) (hy : orderOf y = 4 ∨ orderOf y = 8) :=
    threeQuotient_principalCandidate_all_four_eight S hS x hx e d y
      (by simpa only [Subgroup.orderOf_coe] using hy)
  have hsum₁ : (∑ y : S, d.principalCandidate 1 y) =
      (((d.principalSectionDegree 0 : ℤ) + 5 * d.sign 0 : ℤ) : ℂ) := by
    rw [QuasiDihedral.sum_order_sixteen hS hc (fun y : S => d.principalCandidate 1 y)
      (3 * d.sign 0 : ℤ) (-d.sign 0 : ℤ) (-d.sign 0 : ℤ)
      (fun y hy => (h₂ y hy).1)
      (fun y hy => (h₄₈ y (Or.inl hy)).1)
      (fun y hy => (h₄₈ y (Or.inr hy)).1)]
    change d.principalCandidate 1 1 + _ + _ + _ = _
    rw [threeQuotient_principalCandidate_degree x hx e d]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_add,
      Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast]
    ring
  have hsum₂ : (∑ y : S, d.principalCandidate 2 y) =
      (((d.principalSectionDegree 1 : ℤ) - 13 * d.sign 3 : ℤ) : ℂ) := by
    rw [QuasiDihedral.sum_order_sixteen hS hc (fun y : S => d.principalCandidate 2 y)
      (-3 * d.sign 3 : ℤ) (d.sign 3 : ℤ) (-d.sign 3 : ℤ)
      (fun y hy => (h₂ y hy).2)
      (fun y hy => by simpa only [Subgroup.orderOf_coe, hy, ↓reduceIte] using (h₄₈ y (Or.inl hy)).2)
      (fun y hy => by
        simpa only [Subgroup.orderOf_coe, hy, show (8 : ℕ) ≠ 4 from by decide, if_false]
          using (h₄₈ y (Or.inr hy)).2)]
    change d.principalCandidate 2 1 + _ + _ + _ = _
    rw [threeQuotient_principalCandidate_degree x hx e d]
    simp only [Matrix.cons_val, Int.cast_sub,
      Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast]
    ring
  have hd₁ := (hχ 1).card_dvd_restriction_sum (S : Subgroup G).subtype _ hsum₁
  have hd₂ := (hχ 2).card_dvd_restriction_sum (S : Subgroup G).subtype _ hsum₂
  rw [hc] at hd₁ hd₂
  constructor
  · rcases d.sign_unit 0 with hs | hs <;> rw [hs] at hd₁ ⊢ <;> omega
  · rcases d.sign_unit 3 with hs | hs <;> rw [hs] at hd₂ ⊢ <;> omega
end
end Stellmacher.Recognition
