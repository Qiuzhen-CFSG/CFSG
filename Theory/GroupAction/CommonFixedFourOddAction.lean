module

public import Theory.GroupAction.KleinFourFactorization
public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Odd normal subgroups and a common fixed subgroup for a four-group

Let an elementary four A act on a finite elementary abelian two-group E.
Suppose its three nonidentity elements have the same fixed subgroup F.
Every odd normal subgroup Q of an ambient automorphism group centralizes A.

The three involution centralizers factor Q by the Klein-four coprime-action
formula. Each preserves F, hence Q preserves F. Every element of A fixes F
pointwise and has displacement in F. The automorphisms with these two
properties form a two-group T normalized by Q. Thus [A,Q] lies in both T
and Q and is trivial.

This is the action-theoretic part of the solvable common-fixed-four automizer
argument arising in MacWilliams, Trans. Amer. Math. Soc. (1970),
DOI 10.1090/S0002-9947-1970-0276324-3. The proof uses only elementary
filtration calculations and the proved Klein-four factorization; it does
not use a classification of subgroups of GL(4,2).
-/

open Subgroup
open scoped IsMulCommutative

private theorem odd_normal_preserves_common_fixed
    {E : Type*} [Group E] [Finite E]
    (K : Subgroup (MulAut E)) (A : Subgroup K)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (F : Subgroup E)
    (hfixed : ∀ a : A, a ≠ 1 → ∀ x : E,
      (((a : K) : MulAut E) x = x ↔ x ∈ F))
    (Q : Subgroup K) [Q.Normal] [Finite Q] (hodd : Odd (Nat.card Q)) :
    ∀ q : Q, ∀ x : E, x ∈ F ↔ (q : K) • x ∈ F := by
  let S : Subgroup K :=
    { carrier := {q | ∀ x : E, x ∈ F ↔ q • x ∈ F}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb x
        exact (hb x).trans (by simpa only [mul_smul] using ha (b • x))
      inv_mem' := by
        intro a ha x
        simpa only [smul_inv_smul] using (ha (a⁻¹ • x)).symm }
  let _ : MulDistribMulAction A Q :=
    conjMulDistribMulActionOfLeNormalizer A Q (by rw [normalizer_eq_top]; exact le_top)
  let action : A →* MulAut Q := MulDistribMulAction.toMulAut A Q
  have square (a : A) : a ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
  have invol (a : A) : Function.Involutive (action a) := by
    intro q
    change (action a * action a) q = q
    rw [← map_mul, ← pow_two, square a, map_one]
    rfl
  let _ : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le (α := A)
    (by simp only [ENat.card_eq_coe_natCard, hA]; decide) 1 a
  have hab : a * b ≠ 1 := by
    intro heq
    apply hba
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using square a)
    exact (eq_inv_of_mul_eq_one_right heq).trans hai
  have hcomm : Commute (action a) (action b) := by
    change action a * action b = action b * action a
    rw [← map_mul, ← map_mul, mul_comm a b]
  have fixed_mem (v : A) (hv : v ≠ 1) (q : Q) (hq : action v q = q) :
      (q : K) ∈ S := by
    have hc : Commute (v : K) (q : K) := by
      have hh := congrArg Subtype.val hq
      change (v : K) * (q : K) * (v : K)⁻¹ = (q : K) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    intro x
    rw [← hfixed v hv x, ← hfixed v hv ((q : K) • x)]
    change (v : K) • x = x ↔ (v : K) • ((q : K) • x) = (q : K) • x
    rw [← mul_smul, hc.eq, mul_smul]
    exact (smul_left_cancel_iff (q : K)).symm
  intro q
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ :=
    MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card hodd (action a) (action b)
      (invol a) (invol b) hcomm q
  have hz' : action (a * b) z = z := by simpa only [map_mul] using hz
  have heq' := congrArg Subtype.val heq
  change (q : K) = (x : K) * (y : K) * (z : K) at heq'
  have hqS : (q : K) ∈ S := by
    rw [heq']
    exact S.mul_mem (S.mul_mem (fixed_mem a ha x hx) (fixed_mem b hb y hy))
      (fixed_mem (a * b) hab z hz')
  exact hqS

private theorem centralizes_odd_normal_of_fixed_filtration
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (K : Subgroup (MulAut E)) (A Q : Subgroup K) [Q.Normal]
    (F : Subgroup E) (hodd : Odd (Nat.card Q))
    (hQF : ∀ q : Q, ∀ x : E, x ∈ F ↔ (q : K) • x ∈ F)
    (hAF : ∀ a : A, ∀ x ∈ F, (a : K) • x = x)
    (hdisp : ∀ a : A, ∀ x : E, x⁻¹ * (a : K) • x ∈ F) :
    A ≤ centralizer (Q : Set K) := by
  let T : Subgroup K :=
    { carrier := {t | (∀ x ∈ F, t • x = x) ∧ (∀ x : E, x⁻¹ * t • x ∈ F)}
      one_mem' := by simp
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        constructor
        · intro x hx
          rw [mul_smul, hb x hx, ha x hx]
        · intro x
          have hh : x⁻¹ * (a * b) • x = (x⁻¹ * a • x) * (x⁻¹ * b • x) := by
            calc
              _ = (x⁻¹ * a • x) * (a • (x⁻¹ * b • x)) := by
                simp only [smul_mul', smul_inv', mul_smul, mul_assoc,
                  mul_inv_cancel_left]
              _ = _ := by rw [ha _ (hb' x)]
          rw [hh]
          exact F.mul_mem (ha' x) (hb' x)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        constructor
        · intro x hx
          calc
            a⁻¹ • x = a⁻¹ • (a • x) := congrArg (fun y : E => a⁻¹ • y) (ha x hx).symm
            _ = x := inv_smul_smul a x
        · intro x
          have hh := F.inv_mem (ha' (a⁻¹ • x))
          simpa only [smul_inv_smul, mul_inv_rev, inv_inv] using hh }
  have hinv (x : E) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) x
  have hT : IsPGroup 2 T := by
    intro t
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (t : K) • ((t : K) • x) = x
    have hh := t.property.1 _ (t.property.2 x)
    simp only [smul_mul', hinv] at hh
    exact mul_left_cancel (hh.trans (mul_comm x ((t : K) • x)))
  have conjugate_mem (q : Q) (t : K) (ht : t ∈ T) :
      (q : K) * t * (q : K)⁻¹ ∈ T := by
    constructor
    · intro x hx
      have hy : (q : K)⁻¹ • x ∈ F := (hQF q⁻¹ x).mp hx
      change ((q : K) * t * (q : K)⁻¹) • x = x
      rw [mul_smul, mul_smul, ht.1 _ hy, smul_inv_smul]
    · intro x
      have hy := (hQF q _).mp (ht.2 ((q : K)⁻¹ • x))
      simpa only [smul_mul', smul_inv', smul_inv_smul, mul_smul] using hy
  have hnorm : Q ≤ normalizer (T : Set K) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact conjugate_mem ⟨q, hq⟩ t
    · intro ht
      have hh := conjugate_mem ⟨q⁻¹, Q.inv_mem hq⟩ (q * t * q⁻¹) ht
      simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh
  have hAT : A ≤ T := fun a ha => ⟨hAF ⟨a, ha⟩, hdisp ⟨a, ha⟩⟩
  have hdis : Disjoint T Q := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hcomm : ⁅A, Q⁆ = ⊥ := by
    apply bot_unique
    apply le_trans (le_inf ?_ (commutator_le_right A Q)) hdis.le_bot
    exact (commutator_mono hAT le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hnorm)
  exact commutator_eq_bot_iff_le_centralizer.mp hcomm


/-- A normal odd subgroup centralizes an elementary four whose nonidentity
actors have the same fixed subgroup on a faithful elementary binary module. -/
public theorem odd_normal_centralizes_of_common_fixed_four
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (K : Subgroup (MulAut E)) (A : Subgroup K)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (F : Subgroup E)
    (hfixed : ∀ a : A, a ≠ 1 → ∀ x : E,
      (((a : K) : MulAut E) x = x ↔ x ∈ F))
    (Q : Subgroup K) [Q.Normal] (hodd : Odd (Nat.card Q)) :
    A ≤ centralizer (Q : Set K) := by
  have hinv (x : E) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) x
  apply centralizes_odd_normal_of_fixed_filtration K A Q F hodd
    (odd_normal_preserves_common_fixed K A hA F hfixed Q hodd)
  · intro a x hx
    by_cases ha : a = 1
    · subst a
      exact one_smul K x
    · exact (hfixed a ha x).mpr hx
  · intro a x
    by_cases ha : a = 1
    · subst a
      simpa only [Subgroup.coe_one, one_smul, inv_mul_cancel] using F.one_mem
    · apply (hfixed a ha _).mp
      have hsq : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a
      have hsq' : (a : K) * (a : K) = 1 := by
        exact congrArg Subtype.val (by simpa only [pow_two] using hsq)
      change (a : K) • (x⁻¹ * (a : K) • x) = x⁻¹ * (a : K) • x
      simp only [smul_mul', ← mul_smul, hsq', one_smul, hinv]
      exact mul_comm _ _
