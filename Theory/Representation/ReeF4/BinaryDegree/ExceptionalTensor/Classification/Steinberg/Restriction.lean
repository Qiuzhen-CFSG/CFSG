module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.PRegularSimpleCount

/-!
# Counting reduction for the restricted Ree parameters

This module isolates the finite-group part of Steinberg's restriction theorem.
Once restricted factors are known to be irreducible and distinct, and the
odd-order conjugacy classes of the concrete Ree carrier have the expected
bound, the modular simple-family bound forces every irreducible representation
to occur among the restricted highest weights.  The coordinate-space step is
written for an arbitrary representation universe, as required by the public
classification statement.

The root-action proof of restricted irreducibility, the distinction theorem,
and the concrete semisimple-class bound remain separate source obligations.
They are deliberately explicit hypotheses here: neither the fixed-point
embedding nor an algebraic-group family tag supplies any of these conclusions.

Source: Steinberg, *Representations of Algebraic Groups*, §12.2; GLS3,
Chapter 2, Theorem 2.8.2 and the proof of Theorem 2.8.5.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg

universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] {k : ℕ}

/-- Weights in the restricted range for the odd exceptional power. -/
abbrev RestrictedWeight (k : ℕ) :=
  {a : Weight // InRestrictedRange (2 * k + 1) a}

/-- The source restricted weights are in bijection with the two-bit digits. -/
noncomputable def restrictedWeightEquiv (k : ℕ) :
    (Fin (2 * k + 1) → BasicWeight) ≃ RestrictedWeight k :=
  Equiv.ofBijective (fun b => ⟨parameterWeight _ b, parameterWeight_mem_range _ b⟩)
    ⟨fun b c h => parameterWeight_injective _ (congrArg Subtype.val h), by
      intro a
      obtain ⟨b, hb⟩ := exists_parameterWeight _ a.1 a.2
      exact ⟨b, Subtype.ext hb⟩⟩

noncomputable instance restrictedWeightFintype (k : ℕ) : Fintype (RestrictedWeight k) :=
  Fintype.ofEquiv _ (restrictedWeightEquiv k)

/-- There are exactly `q²` weights for `q = 2^(2*k+1)`. -/
theorem card_restrictedWeight (k : ℕ) : Nat.card (RestrictedWeight k) = 4 ^ (2 * k + 1) := by
  rw [← Nat.card_congr (restrictedWeightEquiv k), Nat.card_fun,
    Nat.card_prod, Nat.card_fin]
  norm_num

/-- Exhaustion from the irreducible restricted family and the concrete
odd-order conjugacy-class bound.  The hypotheses are the exact finite
representation inputs used in Steinberg's completeness argument. -/
theorem exists_restricted_of_simple_family_and_class_bound
    [CharP F 2]
    {j : Model k →* PointGroup F}
    (hbasic : ∀ a : RestrictedWeight k, ∃ A : AlgebraicFactor F,
      HasHighestWeight A a.1)
    (hres : ∀ (A : AlgebraicFactor F) (a : Weight),
      InRestrictedRange (2 * k + 1) a → HasHighestWeight A a →
      Representation.IsIrreducible (A.restrict j).ρ)
    (hrestrict : ∀ (A C : AlgebraicFactor F) (a d : Weight),
      InRestrictedRange (2 * k + 1) a → InRestrictedRange (2 * k + 1) d →
      HasHighestWeight A a → HasHighestWeight C d →
      Nonempty (Representation.Equiv (A.restrict j).ρ (C.restrict j).ρ) →
      AreEquivalentRepresentations A.action C.action)
    (hweights : ∀ (A C : AlgebraicFactor F) (a d : Weight),
      HasHighestWeight A a → HasHighestWeight C d →
      AreEquivalentRepresentations A.action C.action → a = d)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : Model k | ¬ 2 ∣ orderOf g}) ≤ Nat.card (RestrictedWeight k))
    {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F (Model k) W) [Representation.IsIrreducible σ] :
    ∃ (A : AlgebraicFactor F) (a : Weight),
      InRestrictedRange (2 * k + 1) a ∧ HasHighestWeight A a ∧
        Nonempty (Representation.Equiv σ (A.restrict j).ρ) := by
  classical
  let chosen : RestrictedWeight k → AlgebraicFactor F :=
    fun a => Classical.choose (hbasic a)
  have hchosen (a : RestrictedWeight k) : HasHighestWeight (chosen a) a.1 :=
    Classical.choose_spec (hbasic a)
  let rep : ∀ a : RestrictedWeight k,
      Representation F (Model k) (chosen a).Space :=
    fun a => (chosen a).restrict j |>.ρ
  have hirr (a : RestrictedWeight k) : Representation.IsIrreducible (rep a) :=
    hres (chosen a) a.1 a.2 (hchosen a)
  have hpair : ∀ a b : RestrictedWeight k, a ≠ b →
      IsEmpty ((rep a).Equiv (rep b)) := by
    intro a b hab
    constructor
    intro e
    have he := hrestrict (chosen a) (chosen b) a.1 b.1 a.2 b.2
      (hchosen a) (hchosen b) ⟨e⟩
    have heq := hweights (chosen a) (chosen b) a.1 b.1
      (hchosen a) (hchosen b) he
    exact hab (Subtype.ext heq)
  /- Put the arbitrary-universe representation on a coordinate space. -/
  let b := (Module.finBasis F W).equivFun
  let σ' : Representation F (Model k) (Fin (Module.finrank F W) → F) :=
    b.conjRingEquiv.toMonoidHom.comp σ
  let φ : Representation.Equiv σ σ' := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [σ', LinearEquiv.conjRingEquiv])
  have hirrσ' : Representation.IsIrreducible σ' := by
    let f := Representation.IntertwiningMap.equivLinearMapAsModule
      σ σ' φ.toIntertwiningMap
    have hf : Function.Bijective f := φ.toLinearEquiv.bijective
    let ef := LinearEquiv.ofBijective f hf
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    exact ef.isSimpleModule_iff.mp
      ((Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance)
  by_contra! hnone
  let I := RestrictedWeight k
  let M : Option I → Type u := fun i =>
    match i with
    | none => Fin (Module.finrank F W) → F
    | some a => (chosen a).Space
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module F (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let repM : ∀ i, Representation F (Model k) (M i) := fun i =>
    match i with
    | none => σ'
    | some a => rep a
  have finM : ∀ i, FiniteDimensional F (M i) := by
    intro i
    cases i <;> dsimp [M] <;> infer_instance
  have irrM : ∀ i, Representation.IsIrreducible (repM i) := by
    intro i
    cases i with
    | none => exact hirrσ'
    | some a => exact hirr a
  have hpairM : Pairwise fun i j => IsEmpty ((repM i).Equiv (repM j)) := by
    intro i j hij
    constructor
    intro e
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some a => exact (hnone (chosen a) a.1 a.2 (hchosen a)).false (φ.trans e)
    | some a =>
      cases j with
      | none => exact (hnone (chosen a) a.1 a.2 (hchosen a)).false (φ.trans e.symm)
      | some b =>
        exact (hpair a b (fun h => hij (congrArg some h))).false e
  have hb := Representation.irreducible_family_card_le_pRegularConjClasses
    (fun i => M i) (fun i => repM i) 2 hpairM
  have hb' : Nat.card (Option I) ≤ Nat.card I := hb.trans hclasses
  have hfalse : ¬ Nat.card (Option I) ≤ Nat.card I := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  exact hfalse hb'

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
