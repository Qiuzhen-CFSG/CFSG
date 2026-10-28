module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints

/-!
# The small-ratio branch of Janko's first decomposition

The local subgroup and Sylow constraints give `|G| = 40320 h`, where h belongs
to the nineteen-element list in `small_cofactor_mem`. Character orthogonality
fixes the first three exceptional multiplicities for X₂, Z₁ and Z₂. If d is
one of their signed degrees, and a,b are its signed fourth and fifth
multiplicities, the actual Sylow restriction and the strict ratio bound give

* `128 ∣ d + 25 x - 1 + 24 a + 45 b`;
* `4 (7 x + 1 + 8 a + 3 b)^2 < |d|`,

where x is 1 for X₂ and 0 for the two Z characters, and a,b belong to
{-1,0,1}. The unsigned degree divides the actual group order. We enumerate
these divisors using complementary factors up to the square root, proving
that every actual signed degree occurs. A kernel-checked finite calculation
excludes `d(X₂) + d(Z₁) + d(Z₂) = -1` for every cofactor other than 11.
This includes both h = 1 and h = 55 and all nine choices of a,b for each
character. It uses the supplied subgroup constraints followed by degree
elimination uniformly, without further subgroup exclusions.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15,
DOI 10.1016/0021-8693(68)90002-1. The non-strict printed inequalities become
strict by the actual restriction and defect-zero argument in `Boundary`.
-/

open scoped BigOperators
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
open LocalModelDichotomy
noncomputable section
attribute [local instance] Fintype.ofFinite
/- Complementary factors make the exhaustive calculation small; the following
membership lemmas connect it to actual irreducible-degree divisibility. -/
private def divisors (g : ℕ) : List ℕ :=
  ((List.range (g.sqrt + 1)).filter (fun d => 0 < d ∧ d ∣ g)).flatMap
    (fun d => [d, g / d])

private theorem mem_divisors {g n : ℕ} (hg : 0 < g) (hn : n ∣ g) : n ∈ divisors g := by
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn hg
  obtain ⟨m, hm⟩ := hn
  have hm0 : 0 < m := by nlinarith
  rcases Nat.le_sqrt_of_eq_mul hm with h | h
  · apply List.mem_flatMap.mpr
    refine ⟨n, ?_, by simp⟩
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, hn0, ⟨m, hm⟩⟩
  · apply List.mem_flatMap.mpr
    refine ⟨m, ?_, ?_⟩
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hm0, ⟨n, hm.trans (Nat.mul_comm _ _)⟩⟩
    · simp [hm, Nat.mul_div_cancel _ hm0]

private def signedDivisors (g : ℕ) : List ℤ :=
  (divisors g).flatMap (fun (d : ℕ) => [(d : ℤ), -(d : ℤ)])

private theorem mem_signedDivisors {g n : ℕ} (hg : 0 < g) (hn : n ∣ g)
    {s : ℤ} (hs : s = 1 ∨ s = -1) : s * n ∈ signedDivisors g := by
  apply List.mem_flatMap.mpr
  refine ⟨n, mem_divisors hg hn, ?_⟩
  rcases hs with rfl | rfl <;> simp

private def units : List ℤ := [-1, 0, 1]

/- An overestimate of the possible signed degrees: both unprescribed
multiplicities are allowed to vary independently through all unit values. -/
private def rows (g : ℕ) (x : ℤ) : List ℤ :=
  (signedDivisors g).filter fun d =>
    units.any fun a => units.any fun b =>
      decide (128 ∣ d + 25*x - 1 + 24*a + 45*b ∧
        4 * (7*x + 1 + 8*a + 3*b)^2 < (d.natAbs : ℤ))

private theorem mem_rows {g : ℕ} {x d a b : ℤ}
    (hd : d ∈ signedDivisors g) (ha : a = 0 ∨ a = 1 ∨ a = -1)
    (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (hc : 128 ∣ d + 25*x - 1 + 24*a + 45*b)
    (hr : 4 * (7*x + 1 + 8*a + 3*b)^2 < (d.natAbs : ℤ)) : d ∈ rows g x := by
  simp only [rows, List.mem_filter, List.any_eq_true, decide_eq_true_eq]
  refine ⟨hd, a, ?_, b, ?_, hc, hr⟩
  · rcases ha with rfl | rfl | rfl <;> simp [units]
  · rcases hb with rfl | rfl | rfl <;> simp [units]

/- Every cofactor is checked here, including 1 and the inclusive endpoint 55.
For h = 1 the possible signed Z degrees are -210, 84 and 1260; none of
their pairwise sums yields an admissible X₂ degree via degree zero. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem no_degrees :
    ∀ h ∈ ([1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37, 41, 43, 47, 49, 53, 55] : List ℕ),
    h ≠ 11 → ∀ z ∈ rows (40320*h) 0, ∀ w ∈ rows (40320*h) 0,
    -1-z-w ∉ rows (40320*h) 1 := by
  decide +kernel

private theorem scalar_eq_product {G : Type*} [Group G] [Finite G]
    (φ : ClassFunction G) {ψ : ClassFunction G} (hψ : IsIrreducibleCharacter ψ) :
    scalarProduct G φ ψ = characterProduct G φ ψ := by
  obtain ⟨n, ρ, _, rfl⟩ := hψ
  simp only [scalarProduct, characterProduct,
    Representation.representation_character_inv_eq_star_character]

private theorem term_scalar {G : Type*} [Group G] [Finite G] (F : SignedFamily G 7) (i j : Fin 7) :
    scalarProduct G (F.term i) (F.character j) = if i = j then (F.sign i : ℂ) else 0 := by
  rw [SignedFamily.term, scalarProduct_smul_left, scalar_eq_product _ (F.irreducible j)]
  by_cases h : i = j
  · subst j
    have hs := irreducibleCharacter_self (F.irreducible i)
    simp [hs]
  · have hs := irreducibleCharacters_orthogonal (F.irreducible i) (F.irreducible j)
      (fun he => h (F.injective he))
    simp [hs, h]

variable {G : Type*} [Group G] [Finite G]
variable (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
variable (L : LocalAnalysisData D k) (I : SpecialInductionData D k)

/- These are scalar products of the actual functions, obtained from the three
given expansions and orthogonality of the distinct nonprincipal irreducibles. -/
private theorem initial_multiplicities (F : SignedFamily G 7)
    (he0 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (he1 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (he2 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6)
    (r : Fin 7) (hr : r = 1 ∨ r = 5 ∨ r = 6) :
    multiplicities I (F.irreducible r) 0 = F.sign r * (if r = 1 then 1 else 0) ∧
    multiplicities I (F.irreducible r) 1 = 0 ∧
    multiplicities I (F.irreducible r) 2 = F.sign r := by
  have h0 := congrArg (fun ψ => scalarProduct G ψ (F.character r)) he0
  have h1 := congrArg (fun ψ => scalarProduct G ψ (F.character r)) he1
  have h2 := congrArg (fun ψ => scalarProduct G ψ (F.character r)) he2
  have hp : scalarProduct G 1 (F.character r) = 0 := by
    rw [scalar_eq_product _ (F.irreducible r)]
    exact irreducibleCharacters_orthogonal isIrreducibleCharacter_one
      (F.irreducible r) (Ne.symm (F.nonprincipal r))
  simp only [scalarProduct_add_left, term_scalar, hp,
    multiplicities_scalarProduct I (F.irreducible r)] at h0 h1 h2
  rcases hr with rfl | rfl | rfl <;> norm_num [Fin.ext_iff] at h0 h1 h2 ⊢ <;>
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2⟩

include L in
private theorem signed_row (hu : HasUnitMultiplicities I.induced)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (s x : ℤ) (hs : s = 1 ∨ s = -1)
    (h0 : multiplicities I hχ 0 = s*x)
    (h1 : multiplicities I hχ 1 = 0)
    (h2 : multiplicities I hχ 2 = s)
    (hr : involutionRatio I hχ ≤ 1/4) :
    ∃ a b : ℤ, (a = 0 ∨ a = 1 ∨ a = -1) ∧ (b = 0 ∨ b = 1 ∨ b = -1) ∧
      128 ∣ s*hχ.degree + 25*x - 1 + 24*a + 45*b ∧
      4 * (7*x + 1 + 8*a + 3*b)^2 < ((s*hχ.degree).natAbs : ℤ) := by
  let c := multiplicities I hχ
  have hc := degree_congruence_mod128 D k L I hχ c (multiplicities_values I hχ)
  have hu3 := multiplicities_unit I hu hχ 3
  have hu4 := multiplicities_unit I hu hχ 4
  refine ⟨s*c 3, s*c 4, ?_, ?_, ?_, ?_⟩
  · rcases hs with rfl | rfl <;> rcases hu3 with he | he | he <;>
      simp [c, he]
  · rcases hs with rfl | rfl <;> rcases hu4 with he | he | he <;>
      simp [c, he]
  · have hh := dvd_mul_of_dvd_right hc s
    have hh0 : c 0 = s*x := h0
    have hh1 : c 1 = 0 := h1
    have hh2 : c 2 = s := h2
    rw [hh0, hh1, hh2] at hh
    have he : s * ((hχ.degree : ℤ) + 153*(s*x) - 202*0 + 127*s +
        280*c 3 + 45*c 4) =
        (s*hχ.degree + 25*x - 1 + 24*(s*c 3) + 45*(s*c 4)) +
          128*(x+1+2*(s*c 3)) := by
      rcases hs with rfl | rfl <;> ring
    rw [he] at hh
    have hh' := dvd_sub hh (dvd_mul_right (128 : ℤ) (x+1+2*(s*c 3)))
    simpa using hh'
  · have hr' := involutionRatio_lt_of_le L I hχ hr
    have hn : (0 : ℚ) < hχ.degree := by exact_mod_cast hχ.degree_pos
    have ht : (4 : ℚ) * (involutionValue I hχ : ℚ)^2 < hχ.degree := by
      have hh := (div_lt_iff₀ hn).mp hr'
      linarith
    have ht' : 4 * involutionValue I hχ ^2 < (hχ.degree : ℤ) := by exact_mod_cast ht
    have hv : involutionValue I hχ = 7*(s*x) + s + 8*c 3 + 3*c 4 := by
      simp [involutionValue, columnValue, h0, h1, h2, c]
    rw [hv] at ht'
    rcases hs with rfl | rfl
    · simpa using ht'
    · simp only [Int.reduceNeg, neg_mul, one_mul, Int.natAbs_neg, Int.natAbs_natCast] at *
      nlinarith

include L in
/-- Janko's first decomposition with all three small ratios has the Mathieu
order. All cofactor exclusions follow from the actual character constraints. -/
public theorem card_eq_443520_caseOne_small [IsSimpleGroup G]
    (hI : HasSuzukiPairings I) (hu : HasUnitMultiplicities I.induced)
    (F : SignedFamily G 7)
    (he0 : I.induced 0 = F.term 0 + F.term 1 + F.term 2)
    (he1 : I.induced 1 = F.term 0 + F.term 3 + F.term 4)
    (he2 : I.induced 2 = 1 + F.term 1 + F.term 5 + F.term 6)
    (hr1 : involutionRatio I (F.irreducible 1) ≤ 1/4)
    (hr5 : involutionRatio I (F.irreducible 5) ≤ 1/4)
    (hr6 : involutionRatio I (F.irreducible 6) ≤ 1/4) :
    Nat.card G = 443520 := by
  obtain ⟨h, hp, hg, htwo, hthree, hb⟩ :=
    caseOne_smallRatio_cofactor D k L I hI F he2 hr1 hr5 hr6
  by_cases hh : h = 11
  · simpa [hh] using hg
  have hmem := small_cofactor_mem h hp htwo hthree hb
  let d (r : Fin 7) : ℤ := F.sign r * (F.irreducible r).degree
  have hrows (r : Fin 7) (hr : r = 1 ∨ r = 5 ∨ r = 6)
      (hratio : involutionRatio I (F.irreducible r) ≤ 1/4) :
      d r ∈ rows (40320*h) (if r = 1 then 1 else 0) := by
    obtain ⟨hc0, hc1, hc2⟩ :=
      initial_multiplicities (D := D) (k := k) (I := I) F he0 he1 he2 r hr
    obtain ⟨a, b, ha, hb, hc, hlt⟩ :=
      signed_row (D := D) (k := k) (L := L) (I := I) hu (F.irreducible r)
        (F.sign r) (if r = 1 then 1 else 0) (F.sign_eq r) hc0 hc1 hc2 hratio
    apply mem_rows (a := a) (b := b) _ ha hb hc hlt
    apply mem_signedDivisors (by omega) _ (F.sign_eq r)
    rw [← hg]
    exact (F.irreducible r).degree_dvd_card
  have hx : d 1 ∈ rows (40320*h) 1 := by
    simpa using hrows 1 (Or.inl rfl) hr1
  have hz : d 5 ∈ rows (40320*h) 0 := by
    simpa using hrows 5 (Or.inr (Or.inl rfl)) hr5
  have hw : d 6 ∈ rows (40320*h) 0 := by
    simpa using hrows 6 (Or.inr (Or.inr rfl)) hr6
  have hsum : d 1 + d 5 + d 6 = -1 := by
    have he := congrFun he2 1
    have hzero : I.induced 2 1 = 0 := I.degree_zero 2
    rw [hzero] at he
    simp only [Pi.add_apply, Pi.one_apply, SignedFamily.term, Pi.smul_apply,
      smul_eq_mul, (F.irreducible _).degree_eq] at he
    have he' : (0 : ℤ) = 1 + d 1 + d 5 + d 6 := by exact_mod_cast he
    omega
  have heq : -1-d 5-d 6 = d 1 := by omega
  exact False.elim (no_degrees h hmem hh (d 5) hz (d 6) hw (heq ▸ hx))

end
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion
