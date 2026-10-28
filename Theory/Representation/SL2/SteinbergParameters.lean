module

public import Theory.Representation.SL2.HighestWeightUnique
public import Theory.Representation.SL2.HighestWeightDimension
public import Theory.Representation.PRegularSimpleCount
public import Theory.SpecificGroups.SL2.PRegularClasses

/-!
# Classification by Concrete Highest Weights

Let a finite field `K` of characteristic `p` map to an algebraically closed
field `F` of the same characteristic. Every finite-dimensional irreducible
`F`-representation of `SL2(K)` is equivalent to exactly one of the actual
highest-weight orbit spans with degree less than `|K|`.

The orbit spans already give `|K|` pairwise inequivalent simple modules.
If another irreducible were missing, adjoining it would produce a family of
`|K| + 1` pairwise inequivalent simples. The modular simple-family bound and
the count of p-regular SL2 conjugacy classes rule this out. A basis transports
an arbitrary-universe representation to a coordinate space for this finite
family argument; the conclusion is transported back by its actual equivalence.

This supplies the unique restricted-weight parameters used in Fong--Wong,
Nagoya Math. J. 36 (1969), p. 149, formula (1.15). The internal realization is
by concrete orbit spans, with their digit-product dimensions already proved;
no tensor-product classification or character-counting hypothesis is assumed.
Frobenius rotation and prime-field descent are separate subsequent results.
-/

open scoped MatrixGroups

namespace Representation.SL2

universe u

variable {K : Type*} {F V : Type u} [Field K] [Finite K] [Field F] [IsAlgClosed F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem exists_highestWeightSpan_equiv_sameUniverse (e : K →+* F)
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p]
    (ρ : Representation F SL(2,K) V) [ρ.IsIrreducible] :
    ∃ n : Fin (Nat.card K), Nonempty (ρ.Equiv (highestWeightSpan e n.val).toRepresentation) := by
  classical
  by_contra! hnone
  let M : Option (Fin (Nat.card K)) → Type _ := fun i =>
    match i with
    | none => V
    | some n => (highestWeightSpan e n.val).toSubmodule
  let addM : ∀ i, AddCommGroup (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module F (M i) := fun i => by cases i <;> dsimp [M] <;> infer_instance
  let rep : ∀ i, Representation F SL(2,K) (M i) := fun i =>
    match i with
    | none => ρ
    | some n => (highestWeightSpan e n.val).toRepresentation
  have finM : ∀ i, FiniteDimensional F (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    cases i with
    | none => exact inferInstanceAs (IsIrreducible ρ)
    | some n => exact highestWeightSpan_isIrreducible_of_lt_card e n.val n.isLt
  have hne : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro φ
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some m => exact (hnone m).false φ
    | some n =>
      cases j with
      | none => exact (hnone n).false φ.symm
      | some m =>
        apply hij
        congr 1
        exact Fin.ext (highestWeightSpan_equiv_imp_eq e n.val m.val n.isLt m.isLt φ)
  have hbound := Representation.irreducible_family_card_le_pRegularConjClasses M rep p hne
  rw [Matrix.SpecialLinearGroup.card_pRegularConjClasses K p] at hbound
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hbound
  omega

public theorem exists_highestWeightSpan_equiv {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (e : K →+* F)
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p]
    (ρ : Representation F SL(2,K) W) [ρ.IsIrreducible] :
    ∃ n : Fin (Nat.card K), Nonempty (ρ.Equiv (highestWeightSpan e n.val).toRepresentation) := by
  classical
  let b := (Module.finBasis F W).equivFun
  let σ : Representation F SL(2,K) (Fin (Module.finrank F W) → F) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  let φ : ρ.Equiv σ := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [σ, LinearEquiv.conjRingEquiv])
  have hirr : σ.IsIrreducible := by
    let f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap
    have hf : Function.Bijective f := φ.toLinearEquiv.bijective
    let ef := LinearEquiv.ofBijective f hf
    rw [irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mp ((irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance)
  obtain ⟨n, ⟨ψ⟩⟩ := exists_highestWeightSpan_equiv_sameUniverse e p σ
  exact ⟨n, ⟨φ.trans ψ⟩⟩

public theorem existsUnique_highestWeightSpan_equiv {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (e : K →+* F)
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP F p]
    (ρ : Representation F SL(2,K) W) [ρ.IsIrreducible] :
    ∃! n : Fin (Nat.card K), Nonempty (ρ.Equiv (highestWeightSpan e n.val).toRepresentation) := by
  obtain ⟨n, ⟨φ⟩⟩ := exists_highestWeightSpan_equiv e p ρ
  refine ⟨n, ⟨φ⟩, ?_⟩
  intro m hm
  obtain ⟨ψ⟩ := hm
  apply Fin.ext
  exact highestWeightSpan_equiv_imp_eq e m.val n.val m.isLt n.isLt (ψ.symm.trans φ)

end Representation.SL2

