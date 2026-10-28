module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.Basic
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.Relations
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction.FixedSpace

/-!
# Root operators for binary SL₅ upper-fixed vectors

The simple-root operators preserve the upper-fixed subspace. Restricting them
gives idempotent endomorphisms satisfying the type A₄ commutation and braid
relations. Their zero and one eigenvalues are respectively the inactive and
active rank-one alternatives for a local highest vector. The subspace is
nonzero for every nonzero finite-dimensional binary SL₅ module.

The proofs assemble the rank-one calculations of `Basic`, the positive-root
conjugation and rank-two calculations of `Relations`, and the p-group
fixed-vector argument of `FixedSpace`. This is the zero-Hecke construction used
in the highest-vector route to Aschbacher--Smith, *The Classification of
Quasithin Groups*, Lemma I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification.HeckeAction

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The simple zero-Hecke endomorphism of the upper-fixed subspace. -/
def restrictedOperator (ρ : Representation (ZMod 2) Group V) (i : Fin 4) :
    Module.End (ZMod 2) (upperFixedSubmodule ρ) where
  toFun v := ⟨operator ρ i v, operator_upperFixed ρ i v.property⟩
  map_add' v w := Subtype.ext ((operator ρ i).map_add v w)
  map_smul' c v := Subtype.ext ((operator ρ i).map_smul c v)

/-- Restriction agrees with the original root operator in the ambient module. -/
@[simp] theorem restrictedOperator_coe_apply (ρ : Representation (ZMod 2) Group V)
    (i : Fin 4) (v : upperFixedSubmodule ρ) :
    (restrictedOperator ρ i v : V) = operator ρ i v := rfl

/-- Each restricted simple operator is idempotent. -/
theorem restrictedOperator_idempotent (ρ : Representation (ZMod 2) Group V)
    (i : Fin 4) (v : upperFixedSubmodule ρ) :
    restrictedOperator ρ i (restrictedOperator ρ i v) = restrictedOperator ρ i v := by
  exact Subtype.ext (operator_idempotent ρ i v.property)

/-- The quadratic zero-Hecke relation, as an identity of endomorphisms. -/
theorem restrictedOperator_sq (ρ : Representation (ZMod 2) Group V)
    (i : Fin 4) : restrictedOperator ρ i * restrictedOperator ρ i =
      restrictedOperator ρ i := by
  ext v
  exact congrArg Subtype.val (restrictedOperator_idempotent ρ i v)

/-- Simple operators at nonadjacent roots commute on the upper-fixed subspace. -/
theorem restrictedOperator_commute (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 4) (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Commute (restrictedOperator ρ i) (restrictedOperator ρ j) := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (congrArg (fun f : Module.End (ZMod 2) V => f v)
    (operator_commute ρ i j hij).eq)

/-- The adjacent braid relation, as an identity of endomorphisms. -/
theorem restrictedOperator_braid (ρ : Representation (ZMod 2) Group V)
    (i j : Fin 4) (hij : i.val + 1 = j.val) :
    restrictedOperator ρ i * restrictedOperator ρ j * restrictedOperator ρ i =
      restrictedOperator ρ j * restrictedOperator ρ i * restrictedOperator ρ j := by
  apply LinearMap.ext
  intro v
  exact Subtype.ext (operator_braid ρ i j hij v)

/-- Eigenvalue zero on the fixed subspace is the inactive-root alternative. -/
theorem restrictedOperator_eq_zero_iff (ρ : Representation (ZMod 2) Group V)
    (i : Fin 4) (v : upperFixedSubmodule ρ) :
    restrictedOperator ρ i v = 0 ↔ ρ (simpleSwap i) (v : V) = v := by
  rw [← operator_eq_zero_iff ρ i v.property]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Eigenvalue one on the fixed subspace is the active-root alternative. -/
theorem restrictedOperator_eq_self_iff (ρ : Representation (ZMod 2) Group V)
    (i : Fin 4) (v : upperFixedSubmodule ρ) :
    restrictedOperator ρ i v = v ↔
      (v : V) + ρ (simpleSwap i) v + ρ (simpleLower i) v = 0 := by
  rw [← operator_eq_self_iff ρ i v.property]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Nontriviality needed to apply a common-eigenvector theorem to the action. -/
theorem upperFixedSubmodule_nontrivial [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) Group V) : Nontrivial (upperFixedSubmodule ρ) := by
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_upperFixed ρ
  exact ⟨⟨⟨v, hfix⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩

end Representation.SL5TenDimensional.Classification.HeckeAction
