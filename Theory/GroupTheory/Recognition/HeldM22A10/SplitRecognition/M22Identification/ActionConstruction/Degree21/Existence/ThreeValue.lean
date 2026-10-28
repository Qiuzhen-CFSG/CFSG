module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.LocalClasses
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.Character.IntegralRestriction
public import Theory.Character.FiniteOrderTrace


/-!
# Recovering the order-three value from subgroup restrictions

For a genuine degree-21 irreducible with the five special values, averaging
on the actual involution centralizer gives chi(c) = 12m - 9, with m an integer.
Averaging on the elementary Sylow subgroup of order nine gives
9 | 21 + 8 chi(c). These imply chi(c) = 3 modulo 36. The finite-order trace
bound |chi(c)| ≤ 21 forces chi(c) = 3. Thus the five exceptional columns give
all seven literal local values, without assuming a completed character table,
global rationality, or the order of the centralizer of an element of order three.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 5–7, pp.10 and 14–16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open scoped BigOperators
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy CaseII CharacterOrder
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem value_of_conj {χ : ClassFunction G} (hχ : IsClassFunction χ)
    {x y : G} (h : IsConj x y) : χ x = χ y := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp h
  exact (hχ x a).symm

/-- Sum a class function over the actual involution centralizer, using all
seven ambient conjugacy fibers. -/
public theorem centralizer_restriction_sum (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsClassFunction χ) :
    (∑ x : D.centralizer, χ (x : G)) =
      ∑ i : Fin 7, (![1, 51, 32, 84, 72, 96, 48] i : ℂ) *
        χ (into D k (classRepresentative i)) := by
  classical
  let : Fintype D.centralizer := Fintype.ofFinite D.centralizer
  let T (i : Fin 7) := {x : D.centralizer // IsConj (x : G) (into D k (classRepresentative i))}
  let f : (Σ i, T i) → D.centralizer := fun x => x.2.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
      have hxy : x = y := h
      subst y
      have hij : i = j := representatives_separated D k L (hx.symm.trans hy)
      subst j
      rfl
    · intro x
      obtain ⟨i, hi⟩ := centralizer_covered D k L x
      exact ⟨⟨i, x, hi⟩, rfl⟩
  let e := Equiv.ofBijective f hf
  calc
    _ = ∑ x : (Σ i, T i), χ ((e x : D.centralizer) : G) :=
      (e.sum_comp (fun x : D.centralizer => χ (x : G))).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      have hv (x : T i) : χ ((e ⟨i, x⟩ : D.centralizer) : G) =
          χ (into D k (classRepresentative i)) := value_of_conj hχ x.property
      simp_rw [hv]
      have hc : Fintype.card (T i) = ![1, 51, 32, 84, 72, 96, 48] i := by
        rw [← Nat.card_eq_fintype_card]
        exact L.centralizer_distribution i
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
      fin_cases i <;> norm_num

/-- With degree 21 and the five special values, restriction to the centralizer
and to an elementary Sylow nine forces the remaining order-three value. -/
public theorem three_value_of_special_values (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hdegree : χ 1 = 21)
    (hv : ∀ r, χ (into D k (specialRepresentative r)) =
      (![5, -1, -1, 1, 1] r : ℂ)) : χ (into D k c) = 3 := by
  classical
  let : Fintype D.centralizer := Fintype.ofFinite D.centralizer
  have hchar : IsCharacter χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ⟨n, ρ, rfl⟩
  have hclass : IsClassFunction χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ρ.char_conj
  have hs := centralizer_restriction_sum D k L hclass
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  have hv3 := hv 3
  have hv4 := hv 4
  change χ (into D k (z 0)) = 5 at hv0
  change χ (into D k (c * z 0)) = -1 at hv1
  change χ (into D k (z 1 * b * d)) = -1 at hv2
  change χ (into D k (z 3 * a)) = 1 at hv3
  change χ (into D k (z 1 * d)) = 1 at hv4
  have hs' : (∑ x : D.centralizer, χ (x : G)) = 288 + 32 * χ (into D k c) := by
    rw [hs]
    simp only [Fin.sum_univ_succ, classRepresentative, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, map_one, hdegree,
      hv0, hv1, hv2, hv3, hv4]
    norm_num
    ring
  obtain ⟨m, hm⟩ := (isCharacter_comp_hom D.centralizer.subtype hchar).scalarProduct_nat
    isCharacter_one
  simp only [scalarProduct, Pi.one_apply, star_one, mul_one] at hm
  change (Nat.card D.centralizer : ℂ)⁻¹ * (∑ x : D.centralizer, χ (x : G)) = (m : ℂ) at hm
  rw [D.centralizer_card, hs'] at hm
  norm_num only [Nat.cast_ofNat] at hm
  let x : ℤ := 12 * m - 9
  have hx : χ (into D k c) = (x : ℂ) := by
    dsimp only [x]
    push_cast
    linear_combination 12 * hm
  let P : Sylow 3 G := default
  let : Fintype P := Fintype.ofFinite P
  let : IsElementaryAbelian 3 P := (L.sylow_three P).1
  have hPcard : Nat.card P = 9 := (L.sylow_three P).2.1
  have he (a : P) : χ (a : G) = if a = 1 then χ 1 else χ (into D k c) := by
    split_ifs with ha
    · simp [ha]
    · have hao : orderOf (a : G) = 3 := by
        apply orderOf_eq_prime
        · exact elemPow_eq_one_of_isElementaryAbelian (a : G) a.property
        · intro heq
          exact ha (Subtype.ext heq)
      exact value_of_conj hclass (L.three_fusion _ hao)
  have hsum : (∑ a : P, χ (a : G)) = ((21 + 8 * x : ℤ) : ℂ) := by
    simp_rw [he]
    simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq',
      ← Nat.card_eq_fintype_card, hPcard, hdegree, hx]
  have hdiv := hchar.card_dvd_restriction_sum (P : Subgroup G).subtype _ hsum
  rw [hPcard] at hdiv
  have hb : ‖χ (into D k c)‖ ≤ 21 := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    have hn : (n : ℂ) = 21 := by simpa using hdegree
    have hn' : n = 21 := by exact_mod_cast hn
    have hp : ρ (into D k c) ^ orderOf (into D k c) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    simpa [Representation.character, hn'] using
      finite_order_end_norm_trace_le_finrank (ρ (into D k c)) (orderOf_pos _).ne' hp
  have hxbound : |(x : ℝ)| ≤ 21 := by simpa [hx, Complex.norm_intCast] using hb
  have hxl : (-21 : ℤ) ≤ x := by exact_mod_cast (abs_le.mp hxbound).1
  have hxu : x ≤ 21 := by exact_mod_cast (abs_le.mp hxbound).2
  have heq : x = 3 := by dsimp only [x] at *; omega
  simpa [heq] using hx

/-- Complete the seven local columns from the five exceptional columns. -/
public theorem local_values_of_special_values (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hdegree : χ 1 = 21)
    (hv : ∀ r, χ (into D k (specialRepresentative r)) =
      (![5, -1, -1, 1, 1] r : ℂ)) : HasLocalValues D k χ := by
  have hthree := three_value_of_special_values D k L hχ hdegree hv
  intro i
  fin_cases i
  · simpa [classRepresentative, localValues] using hdegree
  · exact hv 0
  · exact hthree
  · exact hv 3
  · exact hv 4
  · exact hv 1
  · exact hv 2
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
