module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.FrobeniusReduction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.RepEquiv

/-!
# Reduction of the exceptional Ree parameter theorem to algebraic restriction

The three results below combine algebraic tensor products, highest weights,
and finite restriction. Existence expands a restricted highest weight into
`2*k+1` two-bit digits, chooses a basic algebraic factor for each digit, and
compares the resulting algebraic tensor with the given extension. Uniqueness
runs this argument backwards: restricted equivalence identifies algebraic
highest weights, and injectivity of the digit expansion identifies the factors.
All comparisons restrict through the actual coefficient embedding.

These are conditional assembly theorems. They do not prove algebraic
highest-weight classification, the exceptional algebraic tensor-product
theorem, or the restricted-range restriction and exhaustion theorems. Their
premises must be discharged before the unconditional Ree parameter theorem,
or the parent factorization theorem, can be asserted.

Sources: GLS3, Theorems 1.14.6, 2.8.2, 2.8.5 and the proof of Corollary
2.8.6(b); Steinberg, *Endomorphisms of Linear Algebraic Groups*, Theorems 13.1
and 13.3. The exceptional endomorphism's full fixed group still has to be
identified with the concrete Ree carrier when applying the source restriction
theorem; an embedding alone does not supply that hypothesis.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] {k : ℕ}
variable (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)

variable
    (htensor : ∀ (B : ZMod (2 * k + 1) → AlgebraicFactor F)
      (b : ZMod (2 * k + 1) → BasicWeight),
      (∀ i, HasBasicHighestWeight (B i) (b i)) →
      ∃ A : AlgebraicFactor F, HasHighestWeight A (tensorWeight b) ∧
        Nonempty (Representation.Equiv (A.restrict (MonoidHom.id _)).ρ (pointTensor ψ B).ρ))

include hψ htensor

/-- Algebraic tensor irreducibility and restricted-range irreducibility imply
irreducibility of every basic tensor on the concrete Ree group. -/
theorem tensor_irreducible_of_restricted
    (hres : ∀ (A : AlgebraicFactor F) (a : Weight),
      InRestrictedRange (2 * k + 1) a → HasHighestWeight A a →
      Representation.IsIrreducible (A.restrict (modelEmbedding f)).ρ)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic) :
    Representation.IsIrreducible (exceptionalTensor (splitEmbedding f) B).ρ := by
  classical
  have hb : ∀ i, ∃ b, HasBasicHighestWeight (B i) b := fun i =>
    (isExceptionalBasic_iff (B i)).mp (hB i)
  choose b hb using hb
  obtain ⟨A, hA, hAe⟩ := htensor B b hb
  obtain ⟨e⟩ := factor_restrict_equiv_tensor f ψ hψ B A hAe
  exact (Representation.RepEquiv.ofRepresentationEquiv e).irreducible_euqiv.mp
    (hres A (tensorWeight b) (tensorWeight_mem_range b) hA)

/-- Restricted-range distinction and uniqueness of weight digits recover each
individual algebraic basic factor from an equivalence of the finite tensors. -/
theorem tensor_unique_of_restricted
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
      AreEquivalentRepresentations B.action C.action)
    (hweights : ∀ (B C : AlgebraicFactor F) (a d : Weight),
      HasHighestWeight B a → HasHighestWeight C d →
      AreEquivalentRepresentations B.action C.action → a = d)
    (hres : ∀ (A C : AlgebraicFactor F) (a d : Weight),
      InRestrictedRange (2 * k + 1) a → InRestrictedRange (2 * k + 1) d →
      HasHighestWeight A a → HasHighestWeight C d →
      Nonempty (Representation.Equiv (A.restrict (modelEmbedding f)).ρ
        (C.restrict (modelEmbedding f)).ρ) →
      AreEquivalentRepresentations A.action C.action)
    (B C : ZMod (2 * k + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic) (hC : ∀ i, (C i).IsExceptionalBasic)
    (he : Nonempty (Representation.Equiv (exceptionalTensor (splitEmbedding f) B).ρ
      (exceptionalTensor (splitEmbedding f) C).ρ)) :
    ∀ i, AreEquivalentRepresentations (B i).action (C i).action := by
  classical
  have hb : ∀ i, ∃ b, HasBasicHighestWeight (B i) b := fun i =>
    (isExceptionalBasic_iff (B i)).mp (hB i)
  have hc : ∀ i, ∃ c, HasBasicHighestWeight (C i) c := fun i =>
    (isExceptionalBasic_iff (C i)).mp (hC i)
  choose b hb using hb
  choose c hc using hc
  obtain ⟨A, hA, hAe⟩ := htensor B b hb
  obtain ⟨D, hD, hDe⟩ := htensor C c hc
  obtain ⟨eA⟩ := factor_restrict_equiv_tensor f ψ hψ B A hAe
  obtain ⟨eD⟩ := factor_restrict_equiv_tensor f ψ hψ C D hDe
  obtain ⟨e⟩ := he
  have hAD := hres A D (tensorWeight b) (tensorWeight c)
    (tensorWeight_mem_range b) (tensorWeight_mem_range c) hA hD
    ⟨(eA.trans e).trans eD.symm⟩
  have hbc := tensorWeight_injective k (hweights A D _ _ hA hD hAD)
  subst c
  intro i
  exact hhigh (B i) (C i) (basicCoefficient (b i)) (hb i) (hc i)

/-- A restricted-range extension is converted into an exceptional tensor by
expanding its weight into digits and realizing those basic weights. -/
theorem exists_tensor_of_restricted
    (hbasic : ∀ b : BasicWeight, ∃ B : AlgebraicFactor F, HasBasicHighestWeight B b)
    (hhigh : ∀ (B C : AlgebraicFactor F) (a : Weight),
      HasHighestWeight B a → HasHighestWeight C a →
      AreEquivalentRepresentations B.action C.action)
    {W : Type v} [AddCommGroup W] [Module F W]
    (σ : Representation F (Model k) W)
    (hex : ∃ (A : AlgebraicFactor F) (a : Weight),
      InRestrictedRange (2 * k + 1) a ∧ HasHighestWeight A a ∧
        Nonempty (Representation.Equiv σ (A.restrict (modelEmbedding f)).ρ)) :
    ∃ B : ZMod (2 * k + 1) → AlgebraicFactor F,
      (∀ i, (B i).IsExceptionalBasic) ∧
      Nonempty (Representation.Equiv σ (exceptionalTensor (splitEmbedding f) B).ρ) := by
  classical
  obtain ⟨A, a, ha, hA, ⟨eA⟩⟩ := hex
  obtain ⟨b, hb⟩ := exists_tensorWeight a ha
  have hB : ∀ i, ∃ B : AlgebraicFactor F, HasBasicHighestWeight B (b i) := fun i => hbasic (b i)
  choose B hB using hB
  obtain ⟨C, hC, hCe⟩ := htensor B b hB
  rw [hb] at hC
  obtain ⟨eAC⟩ := equivalent_restrict (hhigh A C a hA hC) (modelEmbedding f)
  obtain ⟨eC⟩ := factor_restrict_equiv_tensor f ψ hψ B C hCe
  refine ⟨B, fun i => (isExceptionalBasic_iff (B i)).mpr ⟨b i, hB i⟩,
    ⟨(eA.trans eAC).trans eC⟩⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
