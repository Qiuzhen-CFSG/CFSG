module

public import Theory.SpecificGroups.TensorThreeFiveActors.Reduction
public import Theory.SpecificGroups.TensorThreeFiveActors.ProductSplitting
public import Theory.SpecificGroups.TensorThreeFiveActors.FiveFactor

/-!
# Assembly of the two tensor actor models

The product-splitting calculation excludes mixed and diagonal actors; the
five-factor calculation identifies the remaining actor with the actual
Sylow-relative Borel. Together they prove the exact actor dichotomy for every
group actually isomorphic to S₃ × S₅ or S₃ × A₅. The transport in `Reduction`
preserves the three-core, solvable residual and literal relative normalizer.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma 14.4.10(1),
printed p.1010/PDF p.1027; the models are in 14.4.2(5), printed p.1006/PDF p.1023.
-/

@[expose] public section

namespace Theory.SpecificGroups.TensorThreeFiveActors
open Subgroup

/-- Assemble the two concrete tensor models from the independent splitting and
five-point calculations, retaining an actual equivalence with the source group. -/
theorem model_actors_of_factors
    (hs : ProductSplitting (Equiv.Perm (Fin 5)))
    (ha : ProductSplitting (alternatingGroup (Fin 5)))
    (fs : FactorActors (Equiv.Perm (Fin 5)))
    (fa : FactorActors (alternatingGroup (Fin 5)))
    {J : Type*} [Group J] [Finite J]
    (he : Nonempty (J ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ∨
      Nonempty (J ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (Q : Sylow 2 J) (A : Subgroup J)
    (hn : (Q : Subgroup J) ≤ normalizer (A : Set J))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 J ∨ A = solvableResidual J ⊓ normalizer
      (((Q : Subgroup J) ⊓ solvableResidual J : Subgroup J) : Set J) := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    exact actors_of_equiv e
      (product_actors_of_factors TensorThreeFive.s5_threeCore_eq_bot hs fs) Q A hn hp hc
  · obtain ⟨e⟩ := he
    exact actors_of_equiv e
      (product_actors_of_factors TensorThreeFive.a5_threeCore_eq_bot ha fa) Q A hn hp hc

/-- Exhaustive actor classification in either tensor model. The product
splitting and five-factor classification are proved, with no extra premises. -/
theorem model_actors
    {J : Type*} [Group J] [Finite J]
    (he : Nonempty (J ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) ∨
      Nonempty (J ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)))
    (Q : Sylow 2 J) (A : Subgroup J)
    (hn : (Q : Subgroup J) ≤ normalizer (A : Set J))
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A = pCore 3 J ∨ A = solvableResidual J ⊓ normalizer
      (((Q : Subgroup J) ⊓ solvableResidual J : Subgroup J) : Set J) :=
  model_actors_of_factors s5_productSplitting a5_productSplitting
    FiveFactor.symmetric_factorActors FiveFactor.alternating_factorActors he Q A hn hp hc

end Theory.SpecificGroups.TensorThreeFiveActors

end
