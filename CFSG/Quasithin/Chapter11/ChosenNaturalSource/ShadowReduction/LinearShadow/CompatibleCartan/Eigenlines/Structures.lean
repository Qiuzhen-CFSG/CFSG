module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.SourceFields
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.Commutator
/-!
# Inherited field structures on actual ambient subgroups

A field subspace of an abelian ambient subgroup induces a field structure
on its actual image in G. The coordinate map and its scalar equation keep
this structure tied to the literal inclusion. This is used for the three
commutator groups in source 11.3.9, rather than assigning independent scalar
structures to abstractly isomorphic groups.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
variable {G F : Type*} [Group G] [Field F] {P W : Subgroup G}
  [IsMulCommutative P] [Module F (Additive P)]

/-- The actual image of a field subspace is abelian. -/
instance ambientSubgroup_isMulCommutative (U : Submodule F (Additive P)) : IsMulCommutative (ambientSubgroup U) := by
  apply IsMulCommutative.of_setLike_mul_comm
  intro a ha b hb
  exact setLike_mul_comm ((map_subtype_le _) ha) ((map_subtype_le _) hb)

variable [IsMulCommutative W]
/-- Identify the literal ambient subgroup with the subspace it represents. -/
def subgroupFieldCoordinates (U : Submodule F (Additive P)) (hU : ambientSubgroup U = W) :
    Additive W ≃+ U where
  toFun w := ⟨Additive.ofMul ⟨w.toMul, (hU ▸ (show ambientSubgroup U ≤ P from map_subtype_le _)) w.toMul.property⟩,
    (mem_ambientSubgroup U _).mp (hU.symm ▸ w.toMul.property)⟩
  invFun u := Additive.ofMul ⟨u.val.toMul, hU ▸ ((mem_ambientSubgroup U _).mpr u.property)⟩
  left_inv w := rfl
  right_inv u := rfl
  map_add' u v := rfl

/-- Scalars on the literal subgroup are inherited from its ambient subspace. -/
abbrev subgroupFieldModule (U : Submodule F (Additive P)) (hU : ambientSubgroup U = W) :
    Module F (Additive W) := (subgroupFieldCoordinates U hU).module F

/-- The inherited scalars agree with those in the original ambient subgroup. -/
theorem subgroupFieldModule_smul (U : Submodule F (Additive P)) (hU : ambientSubgroup U = W)
    (a : F) (w : Additive W) :
    letI := subgroupFieldModule U hU
    ((a • w).toMul : G) =
      ((a • Additive.ofMul (⟨w.toMul, (hU ▸ (show ambientSubgroup U ≤ P from map_subtype_le _)) w.toMul.property⟩ : P)).toMul : G) := rfl

/-- Restrict an ambient scalar action to the actual subgroup with inherited scalars. -/
theorem scalarConjugation_iff (U : Submodule F (Additive P)) (hU : ambientSubgroup U = W)
    (x : G) (a : F) :
    letI := subgroupFieldModule U hU
    ScalarConjugation W x a ↔
      ∀ u ∈ U, (MulAut.conj x) (u.toMul : G) = ((a • u).toMul : G) := by
  let := subgroupFieldModule U hU
  constructor
  · intro h u hu
    exact h ((subgroupFieldCoordinates U hU).symm ⟨u, hu⟩)
  · intro h w
    exact h _ (subgroupFieldCoordinates U hU w).property
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
