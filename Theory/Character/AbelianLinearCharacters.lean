module

public import Theory.Character.ScalarProductMultiplicity

/-!
# Linear characters and Fourier inversion for finite abelian groups

Complex monoid homomorphisms are exactly the ordinary degree-one characters.
For a finite abelian group every irreducible has degree one, so ordinary
character completeness supplies all homomorphisms, their cardinality,
orthogonality and Fourier inversion. In particular, no externally supplied
character family is needed.

These are the ordinary Fourier inputs to Brauer, *Some applications of the
theory of blocks of characters of finite groups. II* (1964), §VI (6.2)–(6.6).
-/

public section
noncomputable section
open scoped BigOperators IsMulCommutative
attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {A : Type*} [Group A]

/-- A complex homomorphism affords an actual one-dimensional representation. -/
theorem MonoidHom.isLinearCharacter (χ : A →* ℂ) : IsLinearCharacter (χ : A → ℂ) := by
  let ρ : Representation ℂ A (Fin 1 → ℂ) :=
    { toFun := fun g => χ g • (1 : Module.End ℂ (Fin 1 → ℂ))
      map_one' := by simp
      map_mul' := by intro g h; simp [smul_smul, mul_comm] }
  have hirr : Representation.IsIrreducible ρ := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    apply is_simple_module_of_finrank_eq_one (K := ℂ)
    change Module.finrank ℂ (Fin 1 → ℂ) = 1
    simp
  refine ⟨⟨1, ρ, hirr, ?_⟩, χ.map_one⟩
  funext g
  simp [Representation.character, ρ]

/-- A degree-one ordinary character is multiplicative. -/
theorem IsLinearCharacter.map_mul {χ : ClassFunction A} (hχ : IsLinearCharacter χ)
    (g h : A) : χ (g * h) = χ g * χ h := by
  obtain ⟨⟨n, ρ, _, rfl⟩, hdeg⟩ := hχ
  have hn : n = 1 := by simpa [Representation.char_one] using hdeg
  subst n
  simp only [Representation.character, MonoidHom.map_mul,
    LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 1)), LinearMap.toMatrix_mul,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_one]

/-- Bundle a linear ordinary character as a complex homomorphism. -/
@[expose] def IsLinearCharacter.toMonoidHom {χ : ClassFunction A}
    (hχ : IsLinearCharacter χ) : A →* ℂ where
  toFun := χ
  map_one' := hχ.2
  map_mul' := hχ.map_mul

/-- All irreducibles of an abelian group are linear. -/
theorem IsIrreducibleCharacter.isLinear [IsMulCommutative A]
    {χ : ClassFunction A} (hχ : IsIrreducibleCharacter χ) : IsLinearCharacter χ := by
  refine ⟨hχ, ?_⟩
  obtain ⟨n, ρ, hirr, rfl⟩ := hχ
  let := hirr
  rw [Representation.char_one,
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ]
  simp

namespace AbelianLinearCharacters

private theorem ofConj_irreducible [Finite A] {χ : ConjClassFunction A}
    (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

private def familyEquiv [Finite A] [IsMulCommutative A] {ι : Type*} [Fintype ι]
    {χ : ι → ConjClassFunction A} (hχ : IsCompleteIrreducibleCharacterFamily χ) :
    ι ≃ (A →* ℂ) := Equiv.ofBijective
      (fun i => (ofConj_irreducible (hχ.1 i)).isLinear.toMonoidHom) (by
  constructor
  · intro i j hij
    apply hχ.2.2
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    exact DFunLike.congr_fun hij g
  · intro θ
    obtain ⟨n, ρ, hirr, hρ⟩ := θ.isLinearCharacter.1
    obtain ⟨i, hi⟩ := hχ.2.1 (characterClassFunction ρ)
      (isIrreducibleCharacter_characterClassFunction ρ hirr)
    refine ⟨i, ?_⟩
    ext g
    change χ i (ConjClasses.mk g) = θ g
    rw [hi]
    exact (congrFun hρ g).symm)

/-- The collection of all complex linear characters is finite. -/
instance finite [Finite A] [IsMulCommutative A] : Finite (A →* ℂ) := by
  obtain ⟨ι, hι, χ, hχ, _⟩ := card_irreducible_characters_eq_card_conjClasses (G := A)
  let := hι
  exact Finite.of_surjective (familyEquiv hχ) (familyEquiv hχ).surjective

/-- A finite abelian group has exactly its order many ordinary linear characters. -/
theorem card [Finite A] [IsMulCommutative A] : Nat.card (A →* ℂ) = Nat.card A := by
  obtain ⟨ι, hι, χ, hχ, hc⟩ := card_irreducible_characters_eq_card_conjClasses (G := A)
  let := hι
  rw [← Nat.card_congr (familyEquiv hχ), Nat.card_eq_fintype_card, hc]
  exact (Nat.card_congr (Equiv.ofBijective ConjClasses.mk ConjClasses.mk_bijective)).symm

/-- First orthogonality for actual complex homomorphisms. -/
theorem orthogonal [Finite A] (χ ψ : A →* ℂ) :
    scalarProduct A (χ : A → ℂ) (ψ : A → ℂ) = if χ = ψ then 1 else 0 := by
  classical
  by_cases h : χ = ψ
  · subst ψ
    rw [if_pos rfl]
    obtain ⟨n, ρ, hirr, hρ⟩ := χ.isLinearCharacter.1
    rw [hρ]
    exact (irreducible_iff_character_norm_one ρ).mp hirr
  · rw [if_neg h]
    have hne : (χ : A → ℂ) ≠ (ψ : A → ℂ) := fun he => h (DFunLike.coe_injective he)
    have ho := irreducibleCharacters_orthogonal χ.isLinearCharacter.1 ψ.isLinearCharacter.1 hne
    obtain ⟨n, ρ, _, hρ⟩ := ψ.isLinearCharacter.1
    simpa only [scalarProduct, characterProduct, hρ,
      Representation.representation_character_inv_eq_star_character] using ho

/-- Fourier expansion over all actual linear characters of a finite abelian group. -/
theorem expansion [Finite A] [IsMulCommutative A] (f : A → ℂ) (s : A) :
    f s = ∑ χ : A →* ℂ, scalarProduct A f (χ : A → ℂ) * χ s := by
  classical
  obtain ⟨ι, hι, χ, hχ, _⟩ := card_irreducible_characters_eq_card_conjClasses (G := A)
  let := hι
  have hf : IsClassFunction f := by intro x g; simp [mul_comm]
  have hexp := completeFamily_apply_eq_sum_inner hχ (toConjClassFunction f hf) (ConjClasses.mk s)
  rw [toConjClassFunction_apply] at hexp
  simp only [classFunctionInner_toConjClassFunction_right] at hexp
  rw [hexp]
  exact (familyEquiv hχ).sum_comp (fun θ => scalarProduct A f (θ : A → ℂ) * θ s)

/-- The full character sum vanishes away from the identity. -/
theorem sum_apply [Finite A] [IsMulCommutative A] (s : A) :
    ∑ χ : A →* ℂ, χ s = if s = 1 then (Nat.card A : ℂ) else 0 := by
  classical
  let f : A → ℂ := fun t => if t = 1 then (Nat.card A : ℂ) else 0
  have hc (χ : A →* ℂ) : scalarProduct A f (χ : A → ℂ) = 1 := by
    simp [scalarProduct, f, ite_mul]
  simpa only [hc, one_mul] using (expansion f s).symm

/-- Equal nonprincipal Fourier coefficient differences force a constant value
away from one. This is the last Fourier step of Brauer (6.6). -/
theorem eq_neg_of_coeff_sub_one [Finite A] [IsMulCommutative A]
    (f : A → ℂ) (δ : ℂ)
    (h : ∀ χ : A →* ℂ, χ ≠ 1 → scalarProduct A f ((χ : A → ℂ) - 1) = δ)
    (s : A) (hs : s ≠ 1) : f s = -δ := by
  classical
  have hcoeff (χ : A →* ℂ) (hχ : χ ≠ 1) :
      scalarProduct A f (χ : A → ℂ) = δ + scalarProduct A f 1 := by
    have ht := h χ hχ
    simp only [scalarProduct, Pi.sub_apply, Pi.one_apply, star_sub, star_one,
      mul_sub, Finset.sum_sub_distrib, mul_sub] at ht
    have ht : scalarProduct A f (χ : A → ℂ) - scalarProduct A f 1 = δ := by
      simpa only [scalarProduct, Pi.one_apply, star_one, mul_one] using ht
    exact sub_eq_iff_eq_add.mp ht
  have hsum : ∑ χ ∈ (Finset.univ : Finset (A →* ℂ)).erase 1, χ s = -1 := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset (A →* ℂ)) (fun χ => χ s)
      (Finset.mem_univ 1)
    rw [sum_apply, if_neg hs] at hh
    simpa using (eq_neg_iff_add_eq_zero.mpr hh)
  rw [expansion f s, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : A →* ℂ))]
  have he : (∑ χ ∈ (Finset.univ : Finset (A →* ℂ)).erase 1,
      scalarProduct A f (χ : A → ℂ) * χ s) =
      (δ + scalarProduct A f 1) * (-1) := by
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hcoeff χ (Finset.mem_erase.mp hχ).1]
  rw [he]
  change (δ + scalarProduct A f 1) * (-1) + scalarProduct A f 1 * 1 = -δ
  ring

end AbelianLinearCharacters
