module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.Boundary
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiReduction

/-!
# Group-order and character-degree constraints for Janko's exhaustion

The actual E16 normalizer and the nonabelian order-21 subgroup force
`|G| = 40320 h`; the Sylow two- and three-orders make h prime to 2 and 3.
Restriction to the actual Sylow two-group gives the integral degree congruence
with coefficients 153, -202, 127, 280, 45. To justify that restriction sum,
the exceptional induced values separate the five relevant ambient classes,
and their supplied counts exhaust the Sylow group.

The chosen integral multiplicities expose actual character values and the
rational Suzuki identities. For the first decomposition, the small-ratio
inequalities imply h ≤ 55, including the endpoint. Every large ratio bounds
the associated actual degree by 2500. These are constraints for the remaining
exhaustion, not an assertion that the candidates have been eliminated.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15,
DOI 10.1016/0021-8693(68)90002-1. The inequalities on p.15 are non-strict;
`Boundary.ratio_ne_one_quarter` supplies their strict versions here.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy
noncomputable section
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual split E16 normalizer has order 16 · |A6|. -/
public theorem normalizer_E_card (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) :
    Nat.card (normalizer (CaseII.E D k : Set G)) = 5760 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := L.normalizer_E
  have hc := hK.card_mul_card
  have he : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num
  have hE : Nat.card ((CaseII.E D k).subgroupOf
      (normalizer (CaseII.E D k : Set G))) = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (CaseII.E D k).le_normalizer).toEquiv]
    exact L.E_card
  rw [he, hE] at hc
  exact hc.symm

/-- The local subgroups and Sylow orders give the source cofactor factorization. -/
public theorem exists_order_cofactor (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) :
    ∃ h : ℕ, 0 < h ∧ Nat.card G = 40320 * h ∧ ¬ 2 ∣ h ∧ ¬ 3 ∣ h := by
  have he : 5760 ∣ Nat.card G := by
    rw [← normalizer_E_card D k L]
    exact (normalizer (CaseII.E D k : Set G)).card_subgroup_dvd_card
  obtain ⟨A, hA, _⟩ := L.nonabelian_twenty_one
  have ha : 21 ∣ Nat.card G := by
    rw [← hA]
    exact A.card_subgroup_dvd_card
  have hd : 40320 ∣ Nat.card G := by
    have h := Nat.lcm_dvd he ha
    norm_num at h
    simpa only [Nat.card_eq_fintype_card] using h
  obtain ⟨h, hh⟩ := hd
  refine ⟨h, ?_, hh, ?_, ?_⟩
  · have hp := Nat.card_pos (α := G)
    omega
  · have hc := D.sylow.1.card_mul_index
    rw [D.sylow_card, hh] at hc
    have hi : D.sylow.index = 315 * h := by omega
    intro h2
    exact D.sylow.not_dvd_index (hi ▸ dvd_mul_of_dvd_right h2 _)
  · let P : Sylow 3 G := Classical.choice inferInstance
    have hc := P.1.card_mul_index
    rw [(L.sylow_three P).2.1, hh] at hc
    have hi : P.index = 4480 * h := by omega
    intro h3
    exact P.not_dvd_index (hi ▸ dvd_mul_of_dvd_right h3 _)

open scoped BigOperators

private def sylowIndex : Fin 5 → Fin 7 := ![0, 1, 3, 4, 6]

private def sylowSignature : Fin 5 → Fin 5 → ℤ :=
  ![0, fun i => exceptionalValues i 0, fun i => exceptionalValues i 3,
    fun i => exceptionalValues i 4, fun i => exceptionalValues i 2]

private theorem sylowSignature_injective : Function.Injective sylowSignature := by
  decide +kernel

omit [Finite G] in
private theorem classFunction_eq_of_isConj {χ : ClassFunction G}
    (hχ : IsClassFunction χ) {x y : G} (h : IsConj x y) : χ x = χ y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← hg]
  exact (hχ x g).symm

private theorem induction_sylowSignature (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (I : SpecialInductionData D k) (i j : Fin 5) :
    I.induced j (CaseII.into D k (CaseII.classRepresentative (sylowIndex i))) =
      (sylowSignature i j : ℂ) := by
  fin_cases i
  · simpa [sylowIndex, sylowSignature, CaseII.classRepresentative,
      SpecialInductionData.induced] using I.degree_zero j
  · simpa [sylowIndex, sylowSignature, CaseII.classRepresentative,
      SpecialInductionData.induced, specialRepresentative] using I.values j 0
  · simpa [sylowIndex, sylowSignature, CaseII.classRepresentative,
      SpecialInductionData.induced, specialRepresentative] using I.values j 3
  · simpa [sylowIndex, sylowSignature, CaseII.classRepresentative,
      SpecialInductionData.induced, specialRepresentative] using I.values j 4
  · simpa [sylowIndex, sylowSignature, CaseII.classRepresentative,
      SpecialInductionData.induced, specialRepresentative] using I.values j 2

private theorem sylowRepresentative_separated (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (I : SpecialInductionData D k) (i j : Fin 5)
    (h : IsConj (CaseII.into D k (CaseII.classRepresentative (sylowIndex i)))
      (CaseII.into D k (CaseII.classRepresentative (sylowIndex j)))) : i = j := by
  apply sylowSignature_injective
  funext r
  have hf : IsClassFunction (I.induced r) := inducedClassFunction_isClassFunction _ _
  have hh := classFunction_eq_of_isConj hf h
  rw [induction_sylowSignature, induction_sylowSignature] at hh
  exact_mod_cast hh

/-- Evaluate a class function on the actual Sylow two-group, using its five classes. -/
public theorem sylow_restriction_sum (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsClassFunction χ) :
    (∑ x : D.sylow, χ (x : G)) =
      χ 1 + 35 * χ D.z + 36 * χ (CaseII.into D k (specialRepresentative 3)) +
      40 * χ (CaseII.into D k (specialRepresentative 4)) +
      16 * χ (CaseII.into D k (specialRepresentative 2)) := by
  let : Fintype D.sylow := Fintype.ofFinite D.sylow
  classical
  let R (i : Fin 5) := CaseII.into D k (CaseII.classRepresentative (sylowIndex i))
  let T (i : Fin 5) := {x : D.sylow // IsConj (x : G) (R i)}
  let f : (Σ i, T i) → D.sylow := fun x => x.2.1
  have hf : Function.Injective f := by
    rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
    have hxy : x = y := h
    subst y
    have hij : i = j := sylowRepresentative_separated D k I i j (hx.symm.trans hy)
    subst j
    rfl
  have hc : ∀ i, Fintype.card (T i) = ![1, 35, 36, 40, 16] i := by
    intro i
    rw [← Nat.card_eq_fintype_card]
    have hh := L.sylow_distribution (sylowIndex i)
    fin_cases i <;> exact hh
  have hcard : Fintype.card (Σ i, T i) = Fintype.card D.sylow := by
    rw [Fintype.card_sigma, ← Nat.card_eq_fintype_card, D.sylow_card]
    simp [hc, Fin.sum_univ_succ]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)
  have he : (∑ x : D.sylow, χ (x : G)) = ∑ i, (Fintype.card (T i) : ℂ) * χ (R i) := by
    trans ∑ x : (Σ i, T i), χ ((e x : D.sylow) : G)
    · exact (e.sum_comp (fun x : D.sylow => χ (x : G))).symm
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hv : ∀ x : T i, χ ((e ⟨i, x⟩ : D.sylow) : G) = χ (R i) := by
      intro x
      exact classFunction_eq_of_isConj hχ x.property
    simp_rw [hv]
    simp
  rw [he]
  simp [hc, Fin.sum_univ_succ, R, sylowIndex, CaseII.classRepresentative,
    specialRepresentative, CaseII.into_z_zero, add_assoc]

/-- Restriction integrality with the five exceptional columns gives the degree congruence. -/
public theorem degree_congruence_mod128 (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (c : Fin 5 → ℤ)
    (hc : ∀ r, χ (CaseII.into D k (specialRepresentative r)) = (columnValue c r : ℂ)) :
    (128 : ℤ) ∣ (hχ.degree : ℤ) + 153 * c 0 - 202 * c 1 +
      127 * c 2 + 280 * c 3 + 45 * c 4 := by
  let : Fintype D.sylow := Fintype.ofFinite D.sylow
  have hf : IsClassFunction χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ρ.char_conj
  have hchar : IsCharacter χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ⟨n, ρ, rfl⟩
  have hz : χ D.z = (columnValue c 0 : ℂ) := by
    simpa [specialRepresentative, CaseII.into_z_zero] using hc 0
  have hs := sylow_restriction_sum D k L I hf
  rw [hχ.degree_eq, hz, hc 3, hc 4, hc 2] at hs
  have hs' : (∑ x : D.sylow, χ (x : G)) =
      ((hχ.degree : ℤ) + 153 * c 0 - 202 * c 1 +
        127 * c 2 + 280 * c 3 + 45 * c 4 : ℤ) := by
    rw [hs]
    simp [columnValue]
    ring
  have hh := hchar.card_dvd_restriction_sum (D.sylow : Subgroup G).subtype _ hs'
  simpa only [D.sylow_card, Nat.cast_ofNat] using hh

/-- Integral multiplicities chosen from the actual reciprocity calculation. -/
@[expose] public def multiplicities {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    Fin 5 → ℤ := Classical.choose (I.columns χ hχ)

/-- The chosen integers are the actual exceptional scalar products. -/
public theorem multiplicities_scalarProduct {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (i : Fin 5) : scalarProduct G (I.induced i) χ = (multiplicities I hχ i : ℂ) :=
  (Classical.choose_spec (I.columns χ hχ)).1 i

/-- The chosen multiplicities recover the five actual character values. -/
public theorem multiplicities_values {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (i : Fin 5) : χ (CaseII.into D k (specialRepresentative i)) =
      (columnValue (multiplicities I hχ) i : ℂ) :=
  (Classical.choose_spec (I.columns χ hχ)).2 i

/-- The supplied unit-multiplicity theorem bounds the chosen integral row. -/
public theorem multiplicities_unit {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (hu : HasUnitMultiplicities I.induced)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (i : Fin 5) :
    multiplicities I hχ i = 0 ∨ multiplicities I hχ i = 1 ∨
      multiplicities I hχ i = -1 := by
  have hh := hu χ hχ i
  rw [multiplicities_scalarProduct I hχ i] at hh
  exact_mod_cast hh

/-- The integer involution value supplied by the five actual columns. -/
@[expose] public def involutionValue {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) : ℤ :=
  columnValue (multiplicities I hχ) 0

/-- The chosen integer is the value at the distinguished ambient involution. -/
public theorem involutionValue_eq {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    χ D.z = (involutionValue I hχ : ℂ) := by
  simpa [involutionValue, specialRepresentative, CaseII.into_z_zero]
    using multiplicities_values I hχ 0

/-- The unsigned ratio in the inequalities on Janko's p.15. -/
@[expose] public def involutionRatio {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) : ℚ :=
  (involutionValue I hχ : ℚ) ^ 2 / hχ.degree

/-- The unsigned ratio is nonnegative, since irreducible degrees are positive. -/
public theorem involutionRatio_nonneg {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    0 ≤ involutionRatio I hχ := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- The actual E16 restriction excludes the one-quarter equality boundary. -/
public theorem involutionRatio_lt_of_le {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (h : involutionRatio I hχ ≤ 1 / 4) : involutionRatio I hχ < 1 / 4 :=
  lt_of_le_of_ne h (ratio_ne_one_quarter D k L hχ _ (involutionValue_eq I hχ))

/-- Suzuki’s identity over the rationals for an actual integral irreducible expansion. -/
public theorem suzukiOrder_identity_rat (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    {J : Type*} [Fintype J] (χ : J → ClassFunction G)
    (hχ : ∀ j, IsIrreducibleCharacter (χ j)) (a : J → ℤ) (i : Fin 5)
    (he : I.induced i = ∑ j, (a j : ℂ) • χ j) :
    (Nat.card G : ℚ) / 147456 * ∑ j, (a j : ℚ) * involutionRatio I (hχ j) =
      pairingConstants i := by
  have hh := suzukiOrder_identity D k L I hI χ hχ (fun j => (a j : ℂ)) i he
  simp_rw [involutionValue_eq I (hχ _), (hχ _).degree_eq] at hh
  have hr : ((Nat.card G : ℚ) / 147456 *
      ∑ j, (a j : ℚ) * involutionRatio I (hχ j) : ℚ) = pairingConstants i := by
    apply Rat.cast_injective (α := ℂ)
    push_cast
    simpa only [involutionRatio, Rat.cast_div, Rat.cast_pow, Rat.cast_intCast,
      Rat.cast_natCast, mul_div_assoc] using hh
  exact hr

/-- The third Suzuki identity in the first source decomposition, with all signs retained. -/
public theorem caseOne_third_suzuki (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 7)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6) :
    (Nat.card G : ℚ) / 147456 *
      (1 + (F.sign 1 : ℚ) * involutionRatio I (F.irreducible 1) +
        (F.sign 5 : ℚ) * involutionRatio I (F.irreducible 5) +
        (F.sign 6 : ℚ) * involutionRatio I (F.irreducible 6)) = 91 / 12 := by
  let χ : Fin 4 → ClassFunction G := ![1, F.character 1, F.character 5, F.character 6]
  have hc : ∀ i, IsIrreducibleCharacter (χ i) := by
    intro i
    fin_cases i
    · exact isIrreducibleCharacter_one
    · exact F.irreducible 1
    · exact F.irreducible 5
    · exact F.irreducible 6
  have he : I.induced 2 = ∑ i : Fin 4,
      (![1, F.sign 1, F.sign 5, F.sign 6] i : ℂ) • χ i := by
    simpa [χ, Fin.sum_univ_succ, SignedFamily.term, add_assoc] using h3
  have hh := suzukiOrder_identity D k L I hI χ hc
    (fun i => (![1, F.sign 1, F.sign 5, F.sign 6] i : ℂ)) 2 he
  simp only [Fin.sum_univ_succ, χ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Pi.one_apply, Int.cast_one, one_pow, mul_one, div_one, pairingConstants] at hh
  simp_rw [involutionValue_eq I (F.irreducible _), (F.irreducible _).degree_eq] at hh
  apply Rat.cast_injective (α := ℂ)
  push_cast
  simpa [involutionRatio, mul_div_assoc, add_assoc] using hh

/-- The three non-strict small-ratio inequalities in case (1) imply the inclusive bound. -/
public theorem caseOne_smallRatio_cofactor (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) (F : SignedFamily G 7)
    (h3 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6)
    (h1 : involutionRatio I (F.irreducible 1) ≤ 1 / 4)
    (h5 : involutionRatio I (F.irreducible 5) ≤ 1 / 4)
    (h6 : involutionRatio I (F.irreducible 6) ≤ 1 / 4) :
    ∃ h : ℕ, 0 < h ∧ Nat.card G = 40320 * h ∧ ¬ 2 ∣ h ∧ ¬ 3 ∣ h ∧ h ≤ 55 := by
  obtain ⟨h, hp, he, htwo, hthree⟩ := exists_order_cofactor D k L
  refine ⟨h, hp, he, htwo, hthree, ?_⟩
  have h1' := involutionRatio_lt_of_le L I (F.irreducible 1) h1
  have h5' := involutionRatio_lt_of_le L I (F.irreducible 5) h5
  have h6' := involutionRatio_lt_of_le L I (F.irreducible 6) h6
  have p1 := involutionRatio_nonneg I (F.irreducible 1)
  have p5 := involutionRatio_nonneg I (F.irreducible 5)
  have p6 := involutionRatio_nonneg I (F.irreducible 6)
  have hn1 : (1 : ℤ) ≤ (F.irreducible 1).degree := by exact_mod_cast (F.irreducible 1).degree_pos
  have hn5 : (1 : ℤ) ≤ (F.irreducible 5).degree := by exact_mod_cast (F.irreducible 5).degree_pos
  have hn6 : (1 : ℤ) ≤ (F.irreducible 6).degree := by exact_mod_cast (F.irreducible 6).degree_pos
  have hz := congrFun h3 1
  have hzero : I.induced 2 1 = 0 := I.degree_zero 2
  rw [hzero] at hz
  simp only [Pi.add_apply, Pi.one_apply, SignedFamily.term, Pi.smul_apply,
    smul_eq_mul, (F.irreducible _).degree_eq] at hz
  have hz' : (0 : ℤ) = 1 + F.sign 1 * (F.irreducible 1).degree +
      F.sign 5 * (F.irreducible 5).degree + F.sign 6 * (F.irreducible 6).degree := by
    exact_mod_cast hz
  have hs : (1 / 2 : ℚ) <
      1 + (F.sign 1 : ℚ) * involutionRatio I (F.irreducible 1) +
        (F.sign 5 : ℚ) * involutionRatio I (F.irreducible 5) +
        (F.sign 6 : ℚ) * involutionRatio I (F.irreducible 6) := by
    rcases F.sign_eq 1 with s1 | s1 <;> rcases F.sign_eq 5 with s5 | s5 <;>
      rcases F.sign_eq 6 with s6 | s6 <;>
      simp only [s1, s5, s6, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul] at hz' ⊢ <;>
      linarith
  exact cofactor_le55_of_suzuki_sum _ h _ hs he (caseOne_third_suzuki D k L I hI F h3)

/-- Complete cofactor candidates from positivity, the Sylow prime-parts and
the inclusive numerical bound. This does not eliminate any source branch. -/
public theorem small_cofactor_mem (h : ℕ) (hp : 0 < h) (h2 : ¬ 2 ∣ h) (h3 : ¬ 3 ∣ h)
    (hb : h ≤ 55) :
    h ∈ ([1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55] :
      List ℕ) := by
  interval_cases h <;> norm_num at *

/-- Unit exceptional multiplicities give an absolute involution-value bound. -/
public theorem involutionValue_bounds {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (hu : HasUnitMultiplicities I.induced)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    -25 ≤ involutionValue I hχ ∧ involutionValue I hχ ≤ 25 := by
  have hc (i : Fin 5) : -1 ≤ multiplicities I hχ i ∧ multiplicities I hχ i ≤ 1 := by
    rcases multiplicities_unit I hu hχ i with h | h | h <;> omega
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  simp only [involutionValue, columnValue, Matrix.cons_val_zero]
  constructor <;> omega

/-- Every failed small-ratio inequality restricts the actual irreducible degree
to a proved finite range. Further column and restriction constraints sharpen it. -/
public theorem degree_lt2500_of_largeRatio {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) (hu : HasUnitMultiplicities I.induced)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hr : 1 / 4 < involutionRatio I hχ) : hχ.degree < 2500 := by
  obtain ⟨hlo, hhi⟩ := involutionValue_bounds I hu hχ
  have hlo' : (-25 : ℚ) ≤ involutionValue I hχ := by exact_mod_cast hlo
  have hhi' : (involutionValue I hχ : ℚ) ≤ 25 := by exact_mod_cast hhi
  have hd : (0 : ℚ) < hχ.degree := by exact_mod_cast hχ.degree_pos
  have he := (lt_div_iff₀ hd).mp hr
  have hdeg : (hχ.degree : ℚ) < 2500 := by nlinarith
  exact_mod_cast hdeg

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
