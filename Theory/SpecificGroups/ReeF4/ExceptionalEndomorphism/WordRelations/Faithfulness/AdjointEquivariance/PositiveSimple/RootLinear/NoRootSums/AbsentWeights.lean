module

public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basis

/-!
# Vanishing at absent nonzero weights in Geck's Lie algebra

Over an algebraically closed field of characteristic zero, the root-system
isomorphism for Geck's Lie algebra identifies evaluation on each simple Cartan
operator with the original root-coroot pairing. An eigenvector for all those
operators is therefore a weight vector for the whole Cartan subalgebra. If its
weight is nonzero, a nonzero eigenvector would give a root of the Lie algebra;
the isomorphism then gives a root of the original root system.

This proves vanishing for an arbitrary nonzero absent weight, as needed both
for ordinary commutators and for the weight of a quadratic divided commutator.
Lie-algebra membership is essential and remains an explicit hypothesis.

Source: Geck's Lie algebra construction and its root-system identification,
implemented by `RootPairing.GeckConstruction.equivRootSystem` in Mathlib's
`GeckConstruction.Basis`, using Cartan-matrix recognition for reduced
crystallographic root systems.
-/

public section

namespace RootPairing.IntegralGeckConstruction
open Matrix
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R] [IsAlgClosed R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private abbrev weightMap := (RootPairing.GeckConstruction.equivRootSystem b).toHom.weightMap

private lemma weightMap_simple (i : b.support) :
    weightMap (P := P) (b := b) (P.root i) =
      (RootPairing.GeckConstruction.basis b).baseSupp i := by
  let : Module.Free R (RootPairing.GeckConstruction.lieAlgebra b) :=
    Module.Free.of_divisionRing R _
  let : LieAlgebra.IsKilling R (RootPairing.GeckConstruction.lieAlgebra b) :=
    LieAlgebra.HasTrivialRadical.instIsKilling R _
  change (b.toWeightBasis.equiv (RootPairing.GeckConstruction.basis b).base.toWeightBasis
    (RootPairing.GeckConstruction.basis b).baseSupportEquiv) (P.root i) = _
  simp [Module.Basis.equiv]

private lemma weightMap_apply_h (x : M) (i : b.support) :
    weightMap (P := P) (b := b) x (RootPairing.GeckConstruction.h' i) =
      P.toLinearMap x (P.coroot i) := by
  let f : M →ₗ[R] R := (LinearMap.applyₗ (RootPairing.GeckConstruction.h' i)).comp
    (weightMap (P := P) (b := b))
  have hf : f = P.flip.toLinearMap (P.coroot i) := by
    apply b.toWeightBasis.ext
    intro j
    rw [RootPairing.Base.toWeightBasis_apply]
    change weightMap (P := P) (b := b) (P.root j)
      (RootPairing.GeckConstruction.h' i) = P.pairing j i
    rw [weightMap_simple]
    change (RootPairing.GeckConstruction.basis b).baseSupp j
      ((RootPairing.GeckConstruction.basis b).h' i) = _
    rw [LieAlgebra.Basis.baseSupp_apply_h']
    exact RootPairing.Base.algebraMap_cartanMatrixIn_apply (S := ℤ) b j i
  exact LinearMap.congr_fun hf x

/-- A matrix in Geck's Lie algebra with a nonzero weight outside the root system
is zero. The weight may be any vector, not just a sum of two roots. -/
lemma weight_zero_of_absent (x : M) (hx : x ≠ 0)
    (hroot : x ∉ Set.range P.root)
    {X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R}
    (hX : X ∈ RootPairing.GeckConstruction.lieAlgebra b)
    (hweight : ∀ i : b.support, ⁅RootPairing.GeckConstruction.h i, X⁆ =
      P.toLinearMap x (P.coroot i) • X) : X = 0 := by
  let L := RootPairing.GeckConstruction.lieAlgebra b
  let H := RootPairing.GeckConstruction.cartanSubalgebra' b
  let X' : L := ⟨X, hX⟩
  let χ : H →ₗ[R] R := weightMap (P := P) (b := b) x
  have hχ0 : χ ≠ 0 := by
    intro h
    apply hx
    exact (RootPairing.GeckConstruction.equivRootSystem b).bijective_weightMap.1
      (h.trans (map_zero _).symm)
  have heigen (y : H) : ⁅(y : L), X'⁆ = χ y • X' := by
    have hy : y ∈ Submodule.span R (Set.range
        (RootPairing.GeckConstruction.h' (P := P) (b := b))) := by
      rw [RootPairing.GeckConstruction.span_range_h'_eq_top]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        apply Subtype.ext
        change ⁅RootPairing.GeckConstruction.h i, X⁆ =
          χ (RootPairing.GeckConstruction.h' i) • X
        rw [hweight i, show χ (RootPairing.GeckConstruction.h' i) =
          P.toLinearMap x (P.coroot i) from weightMap_apply_h x i]
    | zero => simp
    | add y z _ _ hy hz =>
        rw [show ((↑(y + z) : L)) = (y : L) + (z : L) from map_add H.subtype y z]
        rw [add_lie, map_add, hy, hz, add_smul]
    | smul c y _ hy =>
        rw [show ((↑(c • y) : L)) = c • (y : L) from map_smul H.subtype c y]
        rw [smul_lie, map_smul, hy, smul_smul]
        simp only [smul_eq_mul]
  have hmem : X' ∈ LieModule.genWeightSpace L χ := by
    rw [LieModule.mem_genWeightSpace]
    intro y
    refine ⟨1, ?_⟩
    simp only [pow_one, LinearMap.sub_apply, LieModule.toEnd_apply_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    exact sub_eq_zero.mpr (heigen y)
  by_contra hX0
  have hspace : LieModule.genWeightSpace L χ ≠ ⊥ := by
    intro hbot
    rw [hbot, LieSubmodule.mem_bot] at hmem
    exact hX0 (congrArg Subtype.val hmem)
  let α : H.root := ⟨⟨χ, hspace⟩, by
    simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hzero
    apply hχ0
    apply LinearMap.ext
    intro y
    exact congrFun hzero y⟩
  let e := RootPairing.GeckConstruction.equivRootSystem b
  apply hroot
  refine ⟨e.indexEquiv.symm α, ?_⟩
  apply e.bijective_weightMap.1
  rw [RootPairing.Hom.root_weightMap_apply, e.indexEquiv.apply_symm_apply]
  rfl

end
end RootPairing.IntegralGeckConstruction
