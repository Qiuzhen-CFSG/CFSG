module

public import Theory.Character.AntiRealCoefficients
public import Theory.Character.Multiplicity

/-!
# Recognizing an irreducible from a generalized character

An integral combination of actual complex characters with squared norm one
and positive degree is an actual irreducible character. Expand in the complete
irreducible basis: the integral coefficients have squares summing to one, so
exactly one is nonzero. Positive degree rules out its negative.

This supplies the representation-realization step for the permutation-character
construction of the rational A6 rows in Janko, *A characterization of the
Mathieu simple groups, I*, Section 6, pp.10–11.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

private theorem int_norm_one {ι : Type*} [Fintype ι] (a : ι → ℤ)
    (h : ∑ i, a i * a i = 1) :
    ∃ i, (a i = 1 ∨ a i = -1) ∧ ∀ j, j ≠ i → a j = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at h
  have hle : a i * a i ≤ 1 := by
    calc
      _ ≤ ∑ j, a j * a j := Finset.single_le_sum (fun j _ => mul_self_nonneg (a j)) (Finset.mem_univ i)
      _ = 1 := h
  have hai : a i = 1 ∨ a i = -1 := by
    have : -1 ≤ a i ∧ a i ≤ 1 := by constructor <;> nlinarith
    omega
  refine ⟨i, hai, fun j hji => ?_⟩
  have hjle := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({i, j} : Finset ι)) (fun k _ _ => mul_self_nonneg (a k))
  rw [Finset.sum_pair hji.symm, h] at hjle
  rcases hai with ha | ha <;> rw [ha] at hjle <;> nlinarith [mul_self_nonneg (a j)]

/-- A generalized character of norm one and positive degree is afforded by an
actual irreducible complex representation. -/
public theorem IsGeneralizedCharacter.irreducible_of_norm_one
    {G : Type*} [Group G] [Finite G] {Θ : ClassFunction G}
    (hΘ : IsGeneralizedCharacter Θ) (hnorm : scalarProduct G Θ Θ = 1)
    (hpos : 0 < (Θ 1).re) : IsIrreducibleCharacter Θ := by
  classical
  obtain ⟨ι, hι, ξ, hξ, _b, _hb⟩ := irreducible_characters_form_basis (G := G)
  let : Fintype ι := hι
  let μ : ι → ClassFunction G := fun i => ofConjClassFunction (ξ i)
  have hirr : ∀ i, IsIrreducibleCharacter (μ i) := by
    intro i
    obtain ⟨⟨n, ρ, he⟩, hn⟩ := hξ.1 i
    refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
    · rwa [he] at hn
    · change ofConjClassFunction (ξ i) = ρ.character
      rw [he, ofConjClassFunction_characterClassFunction]
  choose a ha using fun i => hΘ.scalarProduct_irreducible_int (hirr i)
  have hclass : IsClassFunction Θ := by
    obtain ⟨χ, ψ, ⟨n, ρ, rfl⟩, ⟨m, σ, rfl⟩, rfl⟩ := hΘ
    intro x g
    simp only [Pi.sub_apply, Representation.char_conj]
  let Φ := toConjClassFunction Θ hclass
  have hinner (i : ι) : classFunctionInner Φ (ξ i) = (a i : ℂ) := by
    exact (classFunctionInner_toConjClassFunction_right Θ hclass (ξ i)).trans (ha i)
  have hreverse (i : ι) : classFunctionInner (ξ i) Φ = (a i : ℂ) := by
    change scalarProduct G (μ i) Θ = (a i : ℂ)
    rw [← scalarProduct_conj, ha, star_intCast]
  have hexpand : (∑ i, (a i : ℂ) • ξ i) = Φ := by
    simpa only [hinner] using completeFamily_sum_inner_smul_eq hξ Φ
  have hsum : ∑ i, a i * a i = 1 := by
    have h := congrArg (fun f => classFunctionInner f Φ) hexpand
    rw [classFunctionInner_sum_left] at h
    simp only [hreverse, smul_eq_mul] at h
    change ∑ i, (a i : ℂ) * (a i : ℂ) = scalarProduct G Θ Θ at h
    rw [hnorm] at h
    exact_mod_cast h
  obtain ⟨i, hi, hzero⟩ := int_norm_one a hsum
  have heq : Θ = (a i : ℂ) • μ i := by
    ext g
    have heval : Θ g = ∑ k, (a k : ℂ) * μ k g := by
      simpa [μ, Φ, ofConjClassFunction, toConjClassFunction_apply, smul_eq_mul] using
        (congrFun hexpand (ConjClasses.mk g)).symm
    rw [heval, Finset.sum_eq_single i]
    · rfl
    · intro j _ hji
      simp [hzero j hji]
    · simp
  rcases hi with hi | hi
  · rw [heq, hi]
    simpa using hirr i
  · have hdeg := (hξ.1 i).degree_re_pos
    have hneg : Θ 1 = -μ i 1 := by simp [heq, hi]
    rw [hneg, Complex.neg_re] at hpos
    change 0 < (μ i 1).re at hdeg
    linarith
