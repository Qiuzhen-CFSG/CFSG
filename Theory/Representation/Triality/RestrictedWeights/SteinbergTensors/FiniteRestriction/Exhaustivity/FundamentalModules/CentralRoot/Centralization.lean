module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.CentralRoot
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.Basic

/-!
# Highest-root centralization from positive-root commutator containment

The actual root `e₀ + e₁` is the last entry in the standard positive D4 root
order. The linear height functional `3v₀ + 2v₁ + v₂` has value five there
and values between one and five on every positive root. Thus no positive root
is a positive integral combination of this highest root and another positive
root. Positive-root commutator containment then implies pointwise commutation.
For two points in the highest-root group itself, commutation follows directly
from its supplied additive-group parametrization.

The final theorem here is conditional on the shared geometric containment
contract, whose independent construction also serves the root-coordinate
argument. Root arithmetic alone does not prove group commutation. In
particular, this module neither invokes the unresolved Chevalley-system
existence theorem nor asserts unconditional highest-root centralization.

Sources: GLS3, Theorem 1.12.1(b), Theorem 1.12.7(b), and Example 1.14.9(c),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped commutatorElement

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FundamentalModules
open ClassBound.ConnectedCentralizer.Bruhat.Coordinates
open ClassBound.ConnectedCentralizer.Bruhat.Coordinates.Normalization

noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The adjoint construction uses the last root in the actual positive order. -/
public theorem highestRoot_eq_last_positiveRoot (S : Geometry K) :
    highestRoot S = positiveRoot S 11 := rfl

/-- The chosen highest root belongs to the supplied positive root system. -/
public theorem highestRoot_mem_positive (S : Geometry K) :
    highestRoot S ∈ S.roots.positive := by
  rw [highestRoot_eq_last_positiveRoot, S.positive, positiveRoot, Equiv.apply_symm_apply]
  exact Triality.Standard.PositiveCoordinates.rootIndex_positive 11

private def centralizationHeight (v : typeDRootSpan 4) : ℝ :=
  3 * v.val 0 + 2 * v.val 1 + v.val 2

private theorem positiveRoot_height_bounds (i : Fin 12) :
    0 < centralizationHeight ((typeDRootPairing 2).root
      (Triality.Standard.PositiveCoordinates.rootIndex i)) ∧
    centralizationHeight ((typeDRootPairing 2).root
      (Triality.Standard.PositiveCoordinates.rootIndex i)) ≤ 5 := by
  fin_cases i <;>
    norm_num [centralizationHeight, Triality.Standard.PositiveCoordinates.rootIndex,
      Triality.Standard.PositiveCoordinates.difference,
      Triality.Standard.PositiveCoordinates.sumRoot,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

private theorem positive_height_bounds (S : Geometry K) {r : S.roots.Root}
    (hr : r ∈ S.roots.positive) :
    0 < centralizationHeight ((typeDRootPairing 2).root (S.rootIndex r)) ∧
    centralizationHeight ((typeDRootPairing 2).root (S.rootIndex r)) ≤ 5 := by
  have hmem : S.rootIndex r ∈ Set.range Triality.Standard.PositiveCoordinates.rootIndex := by
    rw [Triality.Standard.PositiveCoordinates.range_rootIndex]
    exact (S.positive r).mp hr
  obtain ⟨i, hi⟩ := hmem
  rw [← hi]
  exact positiveRoot_height_bounds i

private theorem highestRoot_height (S : Geometry K) :
    centralizationHeight ((typeDRootPairing 2).root (S.rootIndex (highestRoot S))) = 5 := by
  norm_num [centralizationHeight, highestRoot, highestRootIndex,
    typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
    basisVector, Pi.single_apply, Fin.ext_iff]

/-- There are no correction roots for a positive root and the highest root. -/
public theorem positiveCommutatorRoots_highestRoot_eq_empty (S : Geometry K)
    {r : S.roots.Root} (hr : r ∈ S.roots.positive) :
    positiveCommutatorRoots S r (highestRoot S) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hcpos, i, j, hi, hj, hroot⟩ := hc
  have h := congrArg centralizationHeight hroot
  have hlin : centralizationHeight ((typeDRootPairing 2).root (S.rootIndex c)) =
      (i : ℝ) * centralizationHeight ((typeDRootPairing 2).root (S.rootIndex r)) +
      (j : ℝ) * centralizationHeight
        ((typeDRootPairing 2).root (S.rootIndex (highestRoot S))) := by
    rw [h]
    simp only [centralizationHeight, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [highestRoot_height] at hlin
  have hrheight := (positive_height_bounds S hr).1
  have hcheight := (positive_height_bounds S hcpos).2
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith [mul_pos hi' hrheight]

private theorem rootSubgroup_commute (S : Geometry K) (r : S.roots.Root)
    {x y : Variety.Point K} (hx : x ∈ S.roots.rootSubgroup r)
    (hy : y ∈ S.roots.rootSubgroup r) : Commute x y := by
  let e := (Equiv.mulEquiv (S.roots.rootSubgroup r).pointEquiv).symm.trans
    ((S.rootParameter r).toMulEquiv.symm.trans (Equiv.mulEquiv (additiveGroupPointEquiv k)))
  have h : (⟨x, hx⟩ : (S.roots.rootSubgroup r).toSubgroup) * ⟨y, hy⟩ =
      ⟨y, hy⟩ * ⟨x, hx⟩ := by
    apply e.injective
    simp only [map_mul, mul_comm]
  exact congrArg Subtype.val h

/-- Positive-root commutator containment supplies the precise geometric input
for the central fundamental adjoint construction. Its containment premise must
still be proved from `Geometry` for unconditional highest-root centralization. -/
public theorem positiveCentralizesHighestRoot_of_positiveCommutatorContainment
    (S : Geometry K) (hcomm : PositiveCommutatorContainment S) :
    PositiveCentralizesHighestRoot S := by
  intro r hr x hx y hy
  by_cases heq : r = highestRoot S
  · subst r
    exact rootSubgroup_commute S (highestRoot S) hx hy
  · have hxy := hcomm r hr (highestRoot S) (highestRoot_mem_positive S) heq
      (Subgroup.commutator_mem_commutator hx hy)
    rw [positiveCommutatorRoots_highestRoot_eq_empty S hr,
      RootSubgroupGenerated_empty, Subgroup.mem_bot] at hxy
    exact commutatorElement_eq_one_iff_commute.mp hxy

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FundamentalModules
