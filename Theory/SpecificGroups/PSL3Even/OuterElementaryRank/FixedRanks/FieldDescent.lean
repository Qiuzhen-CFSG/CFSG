module

public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldAction
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.ModelBounds
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent.Conjugacy
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent.FixedQuotient

/-!
# Whole fixed groups of semilinear involutions on PSL₃

An involutory linear–field actor with nontrivial coefficient action has
involutory field part. Scalar norm lifting and quadratic matrix Hilbert–90
construct a general linear conjugator to that pure coefficient action.
Its whole projective fixed subgroup is PSL₃ over the literal fixed subfield:
every fixed projective class has a fixed special linear representative,
and the coefficient inclusion has exactly the smaller scalar center as kernel.

For a field of order `2^f`, the established fixed-field parameter theorem
and the actual PSL₃ two-rank calculation give fixed-group rank `f`.
The case `f = 2`, with binary fixed field, is included. No simplicity,
conjugacy, descent map, or fixed-group identification is assumed.
This discharges the field-identification input of
`FixedRanks.fixed_estimates_of_model_identifications`.

Sources: GLS3, Theorem 2.5.12 and §2.7, `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith E.1.14(1), printed p.214, and 16.1.4(4), printed p.1171.
The latter lists a two-residual; the theorem here proves the stronger whole
fixed-group identification needed by the rank consumer.
-/

public section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks
variable {F : Type*} [Field F] [Finite F]

/-- The whole fixed subgroup of an involutory linear–field actor is the actual
PSL₃ over its fixed subfield. All descent and conjugacy data are constructed. -/
theorem semilinear_field_fixed_equiv (g : GL (Fin 3) F) (σ : F ≃+* F)
    (hne : σ ≠ 1) (hs : (linearConj F g * fieldAction F σ) ^ 2 = 1) :
    Nonempty ((linearConj F g * fieldAction F σ).fixedSubgroup ≃*
      PSL(3, FixedBy.subfield F σ)) := by
  have hσ := field_part_sq g σ hs
  obtain ⟨P, hP⟩ := FieldDescent.exists_linear_conjugate_field g σ
    (orderOf_eq_prime hσ hne) hs
  let e := MulAut.fixedSubgroupCongr (linearConj F P) (linearConj F g * fieldAction F σ)
  exact ⟨e.trans ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hP)).trans
    (FieldDescent.pure_field_fixed_equiv σ hσ))⟩

/-- The exact field-involution fixed-group rank, including original degree two.
This applies the model-rank theorem to the constructed descent equivalence. -/
theorem semilinear_field_fixed_rank {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (g : GL (Fin 3) F) (σ : F ≃+* F) (hne : σ ≠ 1)
    (hs : (linearConj F g * fieldAction F σ) ^ 2 = 1) :
    primeRank 2 (linearConj F g * fieldAction F σ).fixedSubgroup = f := by
  obtain ⟨e⟩ := semilinear_field_fixed_equiv g σ hne hs
  exact field_fixed_rank_of_equiv hf hF _ σ (field_part_sq g σ hs) hne e

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks
