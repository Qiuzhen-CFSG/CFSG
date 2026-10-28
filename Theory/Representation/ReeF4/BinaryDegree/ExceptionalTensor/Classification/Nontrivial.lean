module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration.LinearWitness

/-!
# A nontrivial exceptional factor in a faithful Ree representation

The paired end-root element at parameter one is fixed by the Ree twist and
has a nonzero off-diagonal matrix entry. Thus the concrete model contains a
nonidentity element, including at the binary endpoint. If all algebraic factors
were trivial, their restrictions and tensor product would be trivial. An
intertwining equivalence would then contradict faithfulness on that element.

This is the elementary nontriviality step accompanying the tensor
factorization in GLS3, Corollary 2.8.6(b). It uses the concrete root witness
already established in `SeedGeneration.LinearWitness`, without an order,
perfectness, or simplicity premise.
-/

public section

open Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification
universe u v
open Parabolics.OuterLocal.SuzukiCommutators

/-- An explicit paired end-root element witnesses nontriviality, even at k = 0. -/
theorem exists_model_ne_one (k : ℕ) : ∃ g : Model k, g ≠ 1 := by
  let g : Model k := ⟨endRootWord k 1, by
    apply (mem_fixedSubgroup k _).mpr
    have h := endRootWord_fixed (canonicalLocalBlockInput k) 1
    rwa [LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply] at h⟩
  refine ⟨g, ?_⟩
  intro hg
  exact Parabolics.SeedGeneration.endRootWord_one_ne_one k (congrArg Subtype.val hg)

variable {F : Type u} [Field F]

private theorem tensorPrefix_eq_one {G : Type*} [Group G] (V : ℕ → FDRep F G)
    (g : G) (hV : ∀ i, (V i).ρ g = 1) (n : ℕ) :
    (tensorPrefix V n).ρ g = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change TensorProduct.map ((tensorPrefix V n).ρ g) ((V n).ρ g) = 1
      rw [ih, hV, TensorProduct.map_one]

variable [IsAlgClosed F]

/-- A faithful representation equivalent to the actual exceptional tensor has
at least one nontrivial algebraic factor. -/
theorem exists_nontrivial_factor_of_faithful {k : ℕ}
    {W : Type v} [AddCommGroup W] [Module F W]
    (σ : Representation F (Model k) W) (hσ : Function.Injective σ)
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (e : Representation.Equiv σ (exceptionalTensor ι B).ρ) :
    ∃ i, (B i).IsNontrivial := by
  classical
  by_contra! hB
  have htriv (i : ZMod (2 * k + 1))
      (x : Variety.Point (F4Chevalley.Carrier (k := F))) : (B i).action.action x = 1 := by
    by_contra h
    exact hB i ⟨x, h⟩
  obtain ⟨g, hg⟩ := exists_model_ne_one k
  have htensor : (exceptionalTensor ι B).ρ g = 1 := by
    apply tensorPrefix_eq_one
    intro i
    change (((B (i : ZMod (2 * k + 1))).action.action _).val) = 1
    rw [htriv]
    rfl
  have hσg : σ g = 1 := by
    ext v
    apply e.toLinearEquiv.injective
    change e (σ g v) = e v
    have h := Representation.IntertwiningMap.isIntertwining σ
      (exceptionalTensor ι B).ρ e.toIntertwiningMap g v
    rw [htensor] at h
    exact h
  exact hg (hσ (hσg.trans (map_one σ).symm))

end ReeF4.BinaryDegree.ExceptionalTensor.Classification
