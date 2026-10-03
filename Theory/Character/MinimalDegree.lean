module
public import Theory.Character.IrreducibleDegrees

/-!
# Characters of minimal nonprincipal degree

Character coefficients in a complete irreducible family are natural numbers:
they are dimensions of intertwiner spaces. If the principal coefficient is one,
the degree is `d + 1`, and every nonprincipal irreducible has degree at least
`d > 0`, precisely one nonprincipal constituent occurs, with multiplicity one
and degree `d`. This is the standard degree-counting argument for permutation
characters of small transitive actions.
-/

open scoped BigOperators
open Representation
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Theory.Character
variable {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem irreducible_of_conj {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) : IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

/-- Decompose an actual representation into all irreducibles with natural multiplicities. -/
public theorem exists_natural_character_decomposition (ρ : Representation ℂ G V) :
    ∃ (ι : Type) (_ : Fintype ι) (χ : ι → ClassFunction G) (m : ι → ℕ),
      (∀ i, IsIrreducibleCharacter (χ i)) ∧ Function.Injective χ ∧
      (∀ θ, IsIrreducibleCharacter θ → ∃ i, χ i = θ) ∧
      (∀ i, scalarProduct G ρ.character (χ i) = (m i : ℂ)) ∧
      (∀ g, ρ.character g = ∑ i, (m i : ℂ) * χ i g) := by
  classical
  obtain ⟨ι, hι, χ, hχ, _⟩ := card_irreducible_characters_eq_card_conjClasses (G := G)
  let := hι
  have hm (i : ι) : ∃ m : ℕ,
      classFunctionInner (characterClassFunction ρ) (χ i) = (m : ℂ) := by
    obtain ⟨n, σ, hσ⟩ := (hχ.1 i).1
    let : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
    refine ⟨Module.finrank ℂ (Representation.IntertwiningMap σ ρ), ?_⟩
    rw [hσ, classFunctionInner_characterClassFunction]
    exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := σ) (σ := ρ)
  choose m hm using hm
  refine ⟨ι, hι, fun i => ofConjClassFunction (χ i), m,
    fun i => irreducible_of_conj (hχ.1 i), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply hχ.2.2
    ext C
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    exact congrFun hij g
  · rintro θ ⟨n, σ, hσ, rfl⟩
    obtain ⟨i, hi⟩ := hχ.2.1 (characterClassFunction σ)
      (isIrreducibleCharacter_characterClassFunction σ hσ)
    exact ⟨i, congrArg ofConjClassFunction hi⟩
  · intro i
    exact hm i
  · intro g
    have h := completeFamily_apply_eq_sum_inner hχ (characterClassFunction ρ) (ConjClasses.mk g)
    rw [← ofConjClassFunction_apply (characterClassFunction ρ),
      ofConjClassFunction_characterClassFunction] at h
    simpa only [hm, ofConjClassFunction_apply] using h

private theorem irreducible_one : IsIrreducibleCharacter (1 : ClassFunction G) := by
  have h := irreducible_of_conj
    (isIrreducibleCharacter_characterClassFunction (Representation.trivial ℂ G ℂ)
      trivial_complex_irreducible)
  have he : (Representation.trivial ℂ G ℂ).character = (1 : ClassFunction G) := by
    funext g
    change LinearMap.trace ℂ ℂ (1 : ℂ →ₗ[ℂ] ℂ) = 1
    simp
  simpa only [ofConjClassFunction_characterClassFunction, he] using h

/-- A character with one principal constituent and minimal remaining degree has one
irreducible nonprincipal constituent. -/
public theorem eq_one_add_irreducible_of_min_degree (ρ : Representation ℂ G V)
    (d : ℕ) (hd : 0 < d)
    (hdeg : ρ.character 1 = (d + 1 : ℕ))
    (hprincipal : scalarProduct G ρ.character 1 = 1)
    (hmin : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ ≠ 1 →
      (d : ℝ) ≤ (θ 1).re) :
    ∃ θ : ClassFunction G, IsIrreducibleCharacter θ ∧ θ 1 = (d : ℂ) ∧
      ∀ g, ρ.character g = 1 + θ g := by
  classical
  obtain ⟨ι, hι, χ, m, hirr, hinj, hcover, hcoeff, hsum⟩ := exists_natural_character_decomposition ρ
  let := hι
  obtain ⟨i₀, hi₀⟩ := hcover 1 irreducible_one
  have hm₀ : m i₀ = 1 := by
    have h := hcoeff i₀
    rw [hi₀, hprincipal] at h
    exact_mod_cast h.symm
  let a (i : ι) := (hirr i).degree
  have ha (i : ι) : χ i 1 = (a i : ℂ) := (hirr i).degree_eq
  have ha₀ : a i₀ = 1 := by
    have h := ha i₀
    simp only [hi₀, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hapos (i : ι) : 0 < a i := (hirr i).degree_pos
  have hsumdeg : ∑ i, m i * a i = d + 1 := by
    have h := hsum 1
    rw [hdeg] at h
    simp only [ha] at h
    exact_mod_cast h.symm
  let t := Finset.univ.erase i₀
  have hrest : ∑ i ∈ t, m i * a i = d := by
    have h := Finset.sum_erase_add (Finset.univ) (fun i => m i * a i)
      (Finset.mem_univ i₀)
    rw [hsumdeg, hm₀, ha₀] at h
    dsimp [t]
    omega
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ t, 0 < m j * a j := by
    by_contra! hn
    have hz : ∑ i ∈ t, m i * a i = 0 :=
      Finset.sum_eq_zero (fun i hi => Nat.eq_zero_of_le_zero (hn i hi))
    omega
  have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
  have hjmin : d ≤ a j := by
    have h := hmin (χ j) (hirr j) (fun he => hjne (hinj (he.trans hi₀.symm)))
    rw [ha] at h
    exact_mod_cast h
  have hjle : m j * a j ≤ d := by
    rw [← hrest]
    exact Finset.single_le_sum (f := fun i => m i * a i) (fun i _ => Nat.zero_le _) hj
  have hmj : m j = 1 := by
    have : 0 < m j := Nat.pos_of_mul_pos_right hjpos
    nlinarith
  have haj : a j = d := by nlinarith
  have hzsum : ∑ i ∈ t.erase j, m i * a i = 0 := by
    have h := Finset.sum_erase_add t (fun i => m i * a i) hj
    rw [hrest, hmj, haj] at h
    omega
  have hz (i : ι) (hi : i ∈ t) (hij : i ≠ j) : m i = 0 := by
    have h := (Finset.sum_eq_zero_iff.mp hzsum) i (Finset.mem_erase.mpr ⟨hij, hi⟩)
    exact (Nat.mul_eq_zero.mp h).resolve_right (hapos i).ne'
  refine ⟨χ j, hirr j, by rw [ha, haj], ?_⟩
  intro g
  rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
  change (∑ i ∈ t, (m i : ℂ) * χ i g) + (m i₀ : ℂ) * χ i₀ g = _
  rw [Finset.sum_eq_single j]
  · simp [hmj, hm₀, hi₀, add_comm]
  · intro i hi hij
    simp [hz i hi hij]
  · exact fun hn => (hn hj).elim

end Theory.Character
