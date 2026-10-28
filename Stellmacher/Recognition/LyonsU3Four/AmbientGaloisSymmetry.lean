module

public import Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
public import Stellmacher.Recognition.LyonsU3Four.LocalCentralizerBlocks
public import Theory.Character.GaloisAction
public import Theory.Character.GaloisConjugation
public import Theory.Character.GaloisScalarProduct

/-!
# Galois transport for the ambient Lyons rows

The ordinary rows in a principal congruence block are genuine irreducible
characters.  A characteristic-zero automorphism therefore permutes the rows,
and the permutation preserves their actual degrees.  The block-preservation
input is kept as a named interface: it is the usual Galois invariance of an
ordinary `p`-block, while the character-theoretic transport below is proved
directly from completeness.

For the five local columns, the only additional input is uniqueness of the
genuine section expansion.  This makes the passage from an automorphism
`μ ↦ μ²` to Lyons's displayed four-cycle an equality of actual integral
columns, rather than a formal permutation of arrays.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 374,
385--386.
-/

public section
noncomputable section

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction

namespace Stellmacher.Recognition.LyonsU3Four

public theorem ofConj_irreducible
    {G : Type*} [Group G] [Finite G] {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

public theorem galois_conj_irreducible
    {G : Type*} [Group G] [Finite G] {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) (σ : ℂ ≃+* ℂ) :
    IsIrreducibleConjCharacter (fun c => σ (χ c)) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  let e := Representation.coordinateSemilinearEquiv σ (Fin n)
  let ρ' := ρ.semilinearConjugate σ e
  have hnorm : classFunctionInner (characterClassFunction ρ)
      (characterClassFunction ρ) = 1 := by
    simpa [hρ] using hχ.2
  have hirr : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr hnorm
  have hirr' : Representation.IsIrreducible ρ' :=
    Representation.isIrreducible_semilinearConjugate σ ρ e hirr
  have heq : (fun c => σ (χ c)) = characterClassFunction ρ' := by
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    change σ (χ (ConjClasses.mk g)) = ρ'.character g
    rw [Representation.character_semilinearConjugate]
    simp only [hρ]
    rfl
  refine ⟨⟨n, ρ', heq⟩, ?_⟩
  rw [heq]
  exact (irreducible_iff_character_norm_one ρ').mp hirr'

/-- The row indexed by `i` after applying `σ` to all character values. -/
@[expose] public noncomputable def galoisIndex
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) (i : I) : I :=
  Classical.choose (hχ.2.1 (fun c => σ (χ i c))
    (galois_conj_irreducible (hχ.1 i) σ))

theorem galoisIndex_spec
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) (i : I) :
    χ (galoisIndex χ hχ σ i) = fun c => σ (χ i c) := by
  exact Classical.choose_spec (hχ.2.1 (fun c => σ (χ i c))
    (galois_conj_irreducible (hχ.1 i) σ))

public theorem galoisIndex_injective
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) : Function.Injective (galoisIndex χ hχ σ) := by
  intro i j hij
  apply hχ.2.2
  ext c
  have h := congrArg (fun x : ConjClassFunction G => x c)
    (galoisIndex_spec χ hχ σ i)
  have h' := congrArg (fun x : ConjClassFunction G => x c)
    (galoisIndex_spec χ hχ σ j)
  rw [hij] at h
  exact σ.injective (h.symm.trans h')

public theorem galoisIndex_surjective
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) : Function.Surjective (galoisIndex χ hχ σ) := by
  intro j
  obtain ⟨i, hi⟩ := hχ.2.1 (fun c => σ.symm (χ j c))
    (galois_conj_irreducible (hχ.1 j) σ.symm)
  have hi' : χ (galoisIndex χ hχ σ.symm j) = fun c => σ.symm (χ j c) :=
    galoisIndex_spec χ hχ σ.symm j
  have heq : galoisIndex χ hχ σ (galoisIndex χ hχ σ.symm j) = j := by
    apply hχ.2.2
    ext c
    calc
      χ (galoisIndex χ hχ σ (galoisIndex χ hχ σ.symm j)) c =
          σ (χ (galoisIndex χ hχ σ.symm j) c) :=
        congrArg (fun x : ConjClassFunction G => x c)
          (galoisIndex_spec χ hχ σ (galoisIndex χ hχ σ.symm j))
      _ = σ (σ.symm (χ j c)) := by rw [congrArg (fun x : ConjClassFunction G => x c) hi']
      _ = χ j c := by simp
  exact ⟨galoisIndex χ hχ σ.symm j, heq⟩

/-- The complete-family permutation induced by a field automorphism. -/
@[expose] public noncomputable def galoisPermutation
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) : Equiv.Perm I :=
  Equiv.ofBijective (galoisIndex χ hχ σ)
    ⟨galoisIndex_injective χ hχ σ, galoisIndex_surjective χ hχ σ⟩

theorem galoisPermutation_spec
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) (i : I) (g : G) :
    σ (χ i (ConjClasses.mk g)) =
      χ (galoisPermutation χ hχ σ i) (ConjClasses.mk g) := by
  symm
  exact congrArg (fun x : ConjClassFunction G => x (ConjClasses.mk g))
    (galoisIndex_spec χ hχ σ i)

theorem galoisPermutation_degree
    {G I : Type*} [Group G] [Finite G] [Fintype I]
    (χ : I → ConjClassFunction G)
    (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (σ : ℂ ≃+* ℂ) (i : I) :
    (ofConj_irreducible (hχ.1 (galoisPermutation χ hχ σ i))).degree =
      (ofConj_irreducible (hχ.1 i)).degree := by
  have h1 := galoisPermutation_spec χ hχ σ i (1 : G)
  have hi := (ofConj_irreducible (hχ.1 (galoisPermutation χ hχ σ i))).degree_eq
  have hj := (ofConj_irreducible (hχ.1 i)).degree_eq
  change χ (galoisPermutation χ hχ σ i) (ConjClasses.mk (1 : G)) =
    ((ofConj_irreducible (hχ.1 (galoisPermutation χ hχ σ i))).degree : ℂ) at hi
  change χ i (ConjClasses.mk (1 : G)) =
    ((ofConj_irreducible (hχ.1 i)).degree : ℂ) at hj
  rw [hi, hj] at h1
  have hc :
      ((ofConj_irreducible (hχ.1 i)).degree : ℂ) =
        ((ofConj_irreducible (hχ.1 (galoisPermutation χ hχ σ i))).degree : ℂ) := by
    simpa using h1
  exact_mod_cast hc.symm

open ModularBlock.PrincipalBlockConstruction

/-- A Galois action on the actual rows of a prescribed principal block. -/
structure PrincipalBlockGaloisAction
    {G : Type*} [Group G] [Finite G]
    (b : PrincipalCongruenceBlockData G) (σ : ℂ ≃+* ℂ) where
  perm : Equiv.Perm {i // i ∈ b.block}
  character_eq : ∀ (j : {i // i ∈ b.block}) (g : G),
    σ (b.chi j.1 (ConjClasses.mk g)) =
      b.chi (perm j).1 (ConjClasses.mk g)

/-- Restrict the complete-family permutation once its principal-block closure is
known.  The closure premise is the standard ordinary-block Galois invariance. -/
@[expose] public noncomputable def principalBlockGaloisAction
    {G : Type*} [Group G] [Finite G]
    (b : PrincipalCongruenceBlockData G) (σ : ℂ ≃+* ℂ)
    (hstable : ∀ i,
      i ∈ b.block ↔ galoisPermutation b.chi b.complete σ i ∈ b.block) :
    PrincipalBlockGaloisAction b σ := by
  let p : Equiv.Perm b.I := galoisPermutation b.chi b.complete σ
  let q : Equiv.Perm {i // i ∈ b.block} :=
    { toFun := fun i => ⟨p i, (hstable i.1).mp i.2⟩
      invFun := fun i =>
        ⟨p.symm i.1, (hstable (p.symm i.1)).mpr (by
          change p (p.symm i.1) ∈ b.block
          rw [p.apply_symm_apply]
          exact i.2)⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact p.left_inv i.1
      right_inv := by
        intro i
        apply Subtype.ext
        exact p.right_inv i.1 }
  refine ⟨q, ?_⟩
  intro j g
  simpa [q, p] using galoisPermutation_spec b.chi b.complete σ j.1 g

theorem PrincipalBlockGaloisAction.degree_eq
    {G : Type*} [Group G] [Finite G]
    {b : PrincipalCongruenceBlockData G} {σ : ℂ ≃+* ℂ}
    (a : PrincipalBlockGaloisAction b σ) (j : {i // i ∈ b.block}) :
    (ofConj_irreducible (b.complete.1 (a.perm j).1)).degree =
      (ofConj_irreducible (b.complete.1 j.1)).degree := by
  have h := a.character_eq j (1 : G)
  have hj := (ofConj_irreducible (b.complete.1 j.1)).degree_eq
  have hk := (ofConj_irreducible (b.complete.1 (a.perm j).1)).degree_eq
  change b.chi (a.perm j).1 (ConjClasses.mk (1 : G)) =
    ((ofConj_irreducible (b.complete.1 (a.perm j).1)).degree : ℂ) at hk
  change b.chi j.1 (ConjClasses.mk (1 : G)) =
    ((ofConj_irreducible (b.complete.1 j.1)).degree : ℂ) at hj
  rw [hk, hj] at h
  have hc :
      σ ((ofConj_irreducible (b.complete.1 j.1)).degree : ℂ) =
        ((ofConj_irreducible (b.complete.1 (a.perm j).1)).degree : ℂ) := by
    simpa using h
  rw [map_natCast] at hc
  exact_mod_cast hc.symm

/-- The uniqueness statement for the genuine five-term section expansion.
The displayed `galoisColumn` records the ordered exponents
`[0,1,2,4,3]`; the conclusion is therefore an equality of actual columns. -/
def SectionExpansionUnique
    {G : Type*} [Group G] [Finite G]
    (z : G) (μ : Subgroup.centralizer ({z} : Set G) →* ℂ) : Prop :=
  ∀ (x y : Fin 5 → ℤ),
    (∀ (π : Subgroup.centralizer ({z} : Set G)), Odd (orderOf π) →
      (∑ i, (x i : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent
        (GeneralizedDecompositionData.galoisColumn i)) =
      ∑ i, (y i : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent i) →
    ∀ i, x i = y (GeneralizedDecompositionData.galoisColumn i)

theorem galoisSymmetry_of_principalBlockAction
    {G : Type*} [Group G] [Finite G]
    {b : PrincipalCongruenceBlockData G} {t z : G}
    {μ : Subgroup.centralizer ({z} : Set G) →* ℂ}
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (h31 : c.Equation3_1
      (fun j g => b.chi j.1 (ConjClasses.mk g)) t z μ)
    {σ : ℂ ≃+* ℂ} (a : PrincipalBlockGaloisAction b σ)
    (hμ : ∀ π, σ (μ π) = (μ π) ^ 2)
    (hμpow : ∀ (π : Subgroup.centralizer ({z} : Set G)) (i : Fin 5),
      (μ π) ^ (2 * GeneralizedDecompositionData.basicExponent i) =
        (μ π) ^ GeneralizedDecompositionData.basicExponent
          (GeneralizedDecompositionData.galoisColumn i))
    (huniq : SectionExpansionUnique z μ) :
    c.GaloisSymmetry := by
  let p : Equiv.Perm {j // j ∈ b.block} := a.perm
  refine ⟨p, ?_⟩
  intro j
  have ht := GeneralizedDecompositionData.Equation3_1.at_t c h31 j
  have htp := GeneralizedDecompositionData.Equation3_1.at_t c h31 (p j)
  have hchar := a.character_eq j t
  have hdT : c.dT j = c.dT (p j) := by
    have hc : σ (c.dT j : ℂ) = (c.dT (p j) : ℂ) := by
      calc
        σ (c.dT j : ℂ) = σ (b.chi j.1 (ConjClasses.mk t)) :=
          congrArg σ ht.symm
        _ = b.chi (p j).1 (ConjClasses.mk t) := by simpa using hchar
        _ = (c.dT (p j) : ℂ) := htp
    have hc' : (c.dT j : ℂ) = (c.dT (p j) : ℂ) := by
      simpa only [map_intCast] using hc
    exact_mod_cast hc'
  refine ⟨hdT, ?_⟩
  intro i
  let x : Fin 5 → ℤ := fun k => c.iDz k j
  let y : Fin 5 → ℤ := fun k => c.iDz k (p j)
  have hsum : ∀ (π : Subgroup.centralizer ({z} : Set G)),
      Odd (orderOf π) →
      (∑ k, (x k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent
        (GeneralizedDecompositionData.galoisColumn k)) =
      ∑ k, (y k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent k := by
    intro π hπ
    have hjπ := h31.2 j π hπ
    have hpπ := h31.2 (p j) π hπ
    change b.chi j.1 (ConjClasses.mk (z * (π : G))) = _ at hjπ
    change b.chi (p j).1 (ConjClasses.mk (z * (π : G))) = _ at hpπ
    have hrow :
        σ (∑ k, (x k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent k) =
          ∑ k, (y k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent k := by
      calc
        σ (∑ k, (x k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent k) =
            σ (b.chi j.1 (ConjClasses.mk (z * (π : G)))) := by rw [hjπ]
        _ = b.chi (p j).1 (ConjClasses.mk (z * (π : G))) := by
          simpa using a.character_eq j (z * (π : G))
        _ = ∑ k, (y k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent k := hpπ
    have hleft :
        σ (∑ k, (x k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent k) =
          ∑ k, (x k : ℂ) * μ π ^ GeneralizedDecompositionData.basicExponent
            (GeneralizedDecompositionData.galoisColumn k) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [map_mul, map_pow, hμ, ← pow_mul, hμpow]
      simp
    exact hleft.symm.trans hrow
  exact huniq x y hsum i

end Stellmacher.Recognition.LyonsU3Four
