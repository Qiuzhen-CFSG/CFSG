module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Irreducibility
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceBasicRealization.BasicFactors
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Restriction

/-!
# Exhaustion of the actual finite Ree tensor family by the class count

Choose one genuine algebraic factor for each of the four basic weights and
form all exceptional tensors on the original finite Ree carrier. The proved
root-action theorem makes them irreducible. Finite distinction and algebraic
highest-weight uniqueness make this family pairwise inequivalent, with q²
members. Any missing irreducible module would give q²+1 independent modular
trace characters, contradicting the stated bound on actual odd-order classes.

This discharges finite realization from exactly the two remaining independent
finite source inputs: parameter distinction and the odd-order class bound.
The latter is the literal ConjClasses image, not a substitute torus census.
Arbitrary representation universes are retained by a coordinate equivalence.
Source: Steinberg (1963), 3.9 and 12.2; modular simple-family trace independence.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- Every actual finite irreducible module occurs once the distinct source
family saturates the odd-order class bound. -/
theorem exists_tensor_of_class_bound
    (m : ℕ) (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (f : CoefficientField m →+* F)
    (hunique : ∀ (B C : ZMod (2 * m + 1) → AlgebraicFactor F),
      (∀ i, (B i).IsExceptionalBasic) → (∀ i, (C i).IsExceptionalBasic) →
      Nonempty (Representation.Equiv (exceptionalTensor (splitEmbedding f) B).ρ
        (exceptionalTensor (splitEmbedding f) C).ρ) →
      ∀ i, AreEquivalentRepresentations (B i).action (C i).action)
    (hclasses : Nat.card (ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}) ≤
      Nat.card (RestrictedWeight m))
    {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (σ : Representation F (Model m) W) [Representation.IsIrreducible σ] :
    ∃ B : ZMod (2 * m + 1) → AlgebraicFactor F,
      (∀ i, (B i).IsExceptionalBasic) ∧
      Nonempty (Representation.Equiv σ (exceptionalTensor (splitEmbedding f) B).ρ) := by
  classical
  let I := ZMod (2*m+1) → BasicWeight
  choose basic hbasic using SourceBasicRealization.exists_basic_algebraicFactor (F := F)
  let factors (a : I) : ZMod (2*m+1) → AlgebraicFactor F := fun i => basic (a i)
  have hfactor (a : I) (i) : (factors a i).IsExceptionalBasic :=
    (isExceptionalBasic_iff _).mpr ⟨a i, hbasic (a i)⟩
  let family (a : I) := exceptionalTensor (splitEmbedding f) (factors a)
  have hirr (a : I) : Representation.IsIrreducible (family a).ρ :=
    exceptionalTensor_irreducible m (factors a) hU (hfactor a) f
  have hpair : ∀ a b : I, a ≠ b → IsEmpty (Representation.Equiv (family a).ρ (family b).ρ) := by
    intro a b hab
    refine ⟨fun e => hab (funext fun i => ?_)⟩
    have he := hunique (factors a) (factors b) (hfactor a) (hfactor b) ⟨e⟩ i
    apply basicCoefficient_injective
    exact SourceHighestWeight.highestWeight_eq_of_equivalent _ _ _ _
      (hbasic (a i)) (hbasic (b i)) he
  have hcard : Nat.card I = Nat.card (RestrictedWeight m) := by
    rw [card_restrictedWeight]
    dsimp [I]
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_prod, Nat.card_fin]
  let b := (Module.finBasis F W).equivFun
  let σ' : Representation F (Model m) (Fin (Module.finrank F W) → F) :=
    b.conjRingEquiv.toMonoidHom.comp σ
  let φ : Representation.Equiv σ σ' := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [σ', LinearEquiv.conjRingEquiv])
  have hirrσ' : Representation.IsIrreducible σ' := by
    let j := Representation.IntertwiningMap.equivLinearMapAsModule
      σ σ' φ.toIntertwiningMap
    let ej := LinearEquiv.ofBijective j φ.toLinearEquiv.bijective
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    exact ej.isSimpleModule_iff.mp
      ((Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance)
  by_contra! hnone
  let M : Option I → Type u := fun i =>
    match i with
    | none => Fin (Module.finrank F W) → F
    | some a => (family a).V
  let addM : ∀ i, AddCommGroup (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let modM : ∀ i, Module F (M i) := fun i => by
    cases i <;> dsimp [M] <;> infer_instance
  let repM : ∀ i, Representation F (Model m) (M i) := fun i =>
    match i with
    | none => σ'
    | some a => (family a).ρ
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
      | some a => exact (hnone (factors a) (hfactor a)).false (φ.trans e)
    | some a =>
      cases j with
      | none => exact (hnone (factors a) (hfactor a)).false (φ.trans e.symm)
      | some b => exact (hpair a b (fun h => hij (congrArg some h))).false e
  have hb := Representation.irreducible_family_card_le_pRegularConjClasses
    (fun i => M i) (fun i => repM i) 2 hpairM
  have hb' : Nat.card (Option I) ≤ Nat.card I := by
    rw [hcard]
    exact hb.trans hclasses
  have hfalse : ¬ Nat.card (Option I) ≤ Nat.card I := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  exact hfalse hb'

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
