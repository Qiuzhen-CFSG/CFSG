module

public import Theory.Character.ModularBlock.PrimeCongruence

/-!
# Computing prime congruence blocks by clearing the character degree

For a degree prime to `p`, a central-character congruence can be checked after
multiplication by that degree. The resulting expression is the class size
times the difference between the character value and its degree, all inside
the actual group-order cyclotomic order. A vanishing character value on a
class of size prime to `p` also separates a row from the principal block.

This is the arithmetic form of Feit, *The Representation Theory of Finite
Groups*, IV.4.2, p.150 (the reduced-central-character block criterion).
-/

public section

noncomputable section
namespace ModularBlock.PrimeCongruenceArithmetic
open BlockPreliminaries PrimeBlockConstruction

variable {G : Type*} [Group G] [Finite G]

/-- The contraction of the chosen ideal tests ordinary integer divisibility. -/
theorem natCast_mem_iff {p : ℕ} {A : Type*} [CommRing A] (P : Ideal A)
    (hP : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) (n : ℕ) :
    (n : A) ∈ P ↔ p ∣ n := by
  have h := Ideal.mem_of_liesOver P (Ideal.span ({(p : ℤ)} : Set ℤ)) (n : ℤ)
  have h' : (algebraMap ℤ A) (n : ℤ) ∈ P ↔ p ∣ n := by
    simpa only [Ideal.mem_span_singleton, Int.natCast_dvd_natCast] using h.symm
  convert h' using 1
  norm_cast

/-- Every ordinary character value belongs to the group-order cyclotomic order. -/
theorem characterValue_mem {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (χ : ConjClassFunction G) (hχ : IsConjCharacter χ) (C : ConjClasses G) :
    χ C ∈ cyclotomicOrder η := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  exact representation_character_mem_cyclotomicOrder hη ρ g

/-- An ordinary character value in the actual cyclotomic order. -/
@[expose] def characterValue {η : ℂ} (hη : IsPrimitiveRoot η (Nat.card G))
    (χ : ConjClassFunction G) (hχ : IsConjCharacter χ) (C : ConjClasses G) :
    cyclotomicOrder η := ⟨χ C, characterValue_mem hη χ hχ C⟩

/-- The principal central character is the conjugacy-class size. -/
theorem principal_centralCharacter {p : ℕ} (d : PrimeCongruenceBlockData p G)
    (C : ConjClasses G) :
    centralCharacterInCyclotomicOrder d.eta_spec (d.chi d.principal)
      (d.complete.1 d.principal) C = (Nat.card C.carrier : cyclotomicOrder d.eta) := by
  apply Subtype.ext
  simp [centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue,
    d.principal_eq, PrincipalBlockConstruction.ordinaryPrincipalCharacter]

/-- Clear a degree prime to `p` in the principal-block congruence criterion. -/
theorem mem_block_iff_of_degree {p n : ℕ} (d : PrimeCongruenceBlockData p G)
    (i : d.I) (hd : d.chi i (ConjClasses.mk 1) = (n : ℂ)) (hn : ¬ p ∣ n) :
    i ∈ d.block ↔ ∀ C : ConjClasses G,
      (Nat.card C.carrier : cyclotomicOrder d.eta) *
        (characterValue d.eta_spec (d.chi i) (d.complete.1 i).1 C - n) ∈ d.primeIdeal := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  rw [PrimeCongruenceBlockData.block, d.mem_blockOf_iff_centralCharacter]
  apply forall_congr'
  intro C
  rw [principal_centralCharacter]
  have heq : (n : cyclotomicOrder d.eta) *
      (centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) (d.complete.1 i) C -
        (Nat.card C.carrier : cyclotomicOrder d.eta)) =
      (Nat.card C.carrier : cyclotomicOrder d.eta) *
        (characterValue d.eta_spec (d.chi i) (d.complete.1 i).1 C - n) := by
    apply Subtype.ext
    simp [characterValue, centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue, hd]
    field_simp
  rw [← heq]
  constructor
  · exact d.primeIdeal.mul_mem_left _
  · intro h
    exact (d.primeIdeal_maximal.isPrime.mem_or_mem h).resolve_left
      (fun h => hn ((natCast_mem_iff d.primeIdeal d.primeIdeal_liesOver n).mp h))

/-- Vanishing on a class of size prime to `p` excludes the principal block. -/
theorem not_mem_block_of_vanish {p : ℕ} (d : PrimeCongruenceBlockData p G)
    (i : d.I) (C : ConjClasses G) (hsize : ¬ p ∣ Nat.card C.carrier)
    (hzero : d.chi i C = 0) : i ∉ d.block := by
  intro hi
  have h := (d.mem_blockOf_iff_centralCharacter i d.principal).mp hi C
  rw [principal_centralCharacter] at h
  have hz : centralCharacterInCyclotomicOrder d.eta_spec (d.chi i) (d.complete.1 i) C = 0 := by
    apply Subtype.ext
    simp [centralCharacterInCyclotomicOrder, ordinaryCentralCharacterValue, hzero]
  rw [hz, zero_sub, d.primeIdeal.neg_mem_iff] at h
  exact hsize ((natCast_mem_iff d.primeIdeal d.primeIdeal_liesOver _).mp h)
end ModularBlock.PrimeCongruenceArithmetic
