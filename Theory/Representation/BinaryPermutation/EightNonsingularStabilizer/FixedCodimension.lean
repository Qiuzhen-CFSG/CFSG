module
public import Theory.Representation.BinaryPermutation.EightNonsingularStabilizer.MovedCore
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Fixed codimension of the nonsingular point residual

The two-point fixer moves the five-dimensional core on the complementary
six letters. The natural quotient is injective on that core, so it still
has moved dimension five. Self-duality of the original permutation section
identifies this dimension with its fixed codimension. The actor and both
quotient maps are unchanged.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.EightNonsingular

/-- The original two-point fixer's fixed quotient has dimension five. -/
theorem pointFixer_fixedCodim (i j : Fin 8) (hij : i ≠ j) :
    fixedCodim (alternatingNaturalRepresentation (Fin 8)) (pointFixer i j) = 5 := by
  let σ : Representation (ZMod 2) (pointFixer i j) (core (Fin 8)) := (alternatingCoreRepresentation (Fin 8)).comp (pointFixer i j).subtype
  let ρ : Representation (ZMod 2) (pointFixer i j) (natural (Fin 8)) := (alternatingNaturalRepresentation (Fin 8)).comp (pointFixer i j).subtype
  let f : σ.IntertwiningMap ρ :=
    (coreToNatural (Fin 8)).intertwiningMap_of_isIntertwiningMap σ ρ
      (fun a w => coreToNatural_equivariant a.val.val w)
  have hm := OneCohomology.map_coinvariants_of_surjective f coreToNatural_surjective
  have hdim : Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 5 := by
    rw [←hm,pointFixer_moved_core i j hij]
    change Module.finrank (ZMod 2) ((extendSix i j hij).range.map (coreToNatural (Fin 8))) = 5
    rw [←LinearMap.range_comp,LinearMap.finrank_range_of_inj (toNatural_extendSix_injective i j hij),finrank_core]
    rfl
  have he := fixedCodim_map_equivariant (alternatingNaturalRepresentation (Fin 8))
    (alternatingNaturalRepresentation (Fin 8)).dual (MonoidHom.id _)
    (naturalDualEquiv (Fin 8)) (fun a w => naturalDualEquiv_equivariant (Fin 8) a.val w)
    (pointFixer i j)
  rw [Subgroup.map_id,fixedCodim_dual_eq_moved_finrank,subspaceCommutator_top_eq_coinvariants] at he
  exact he.trans hdim
end BinaryPermutation.EightNonsingular
