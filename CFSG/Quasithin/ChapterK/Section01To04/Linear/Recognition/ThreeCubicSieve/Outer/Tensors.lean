module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Estimate
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords

/-!
# Assembly of the remaining Schur-linear SL₃ tensor estimates

The tensor-exchange fixed-space calculation and both geometric constructions
are complete. This assembly combines the exchange model for words containing a
natural or dual factor with the displacement bound for the remaining
pure-adjoint tensors. The single adjoint is handled by the separate branch in
`Outer.Remaining`.
Source: GM, Classification of 2F-modules II, Proposition 4.8, manuscript
pp.26–28, used in Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The exchange and pure-adjoint estimates assemble for all remaining words. -/
theorem tensor_estimate_of_swap_models_and_adjoint_tensors
    (hswap : Tensors.NaturalSwapModels B σ) (hadj : Tensors.AdjointTensorDisplacement B σ) :
    SchurLinearTensorEstimate B σ := by
  intro M hp hn hj A hA hc hr ho hs
  by_cases ha : naturalCount M.block = 0
  · exact Tensors.adjointTensorEstimate_of_displacement hadj
      M ha (by omega) hj A hA hc hr ho hs
  · obtain ⟨R⟩ := hswap M (by omega) hn A hA hc hr ho hs
    exact R.estimate M hp hn hj hr

/-- Every non-small word other than the single adjoint excludes an elementary
cubic outer actor that is linear over the original Schur field. The central
kernel supplies both geometric constructions, with no extra model premise. -/
theorem tensor_estimate (hk : σ.ker ≤ Subgroup.center SL(3,B.Carrier)) :
    SchurLinearTensorEstimate B σ :=
  tensor_estimate_of_swap_models_and_adjoint_tensors B σ
    (Tensors.Realization.natural_swap_models hk)
    (Tensors.adjointTensorDisplacement hk)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer
