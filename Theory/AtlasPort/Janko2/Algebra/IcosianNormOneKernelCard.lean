/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormOneKernelCard.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneKernel
public import Mathlib.Data.Fintype.Card

/-!
# IcosianNormOneKernelCard

The kernel of norm-one reduction consists of the two distinct signs.
An explicit equivalence with Bool gives its cardinality two.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormOneKernelCard.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra Matrix

def icosianNormOneMinusOne : icosianNormOneGroup :=
  icosianNormOneGroupOf (-1) (icosianOrder.neg_mem icosianOrder.one_mem) (by
    change Quaternion.normSq (-1 : IcosianQuaternion)=1
    rw [Quaternion.normSq_neg,map_one])

theorem icosianNormOne_value_injective :
    Function.Injective (fun u : icosianNormOneGroup => u.val.val) := by
  intro u v h
  apply Subtype.ext
  exact Subtype.ext h

theorem icosianNormOneMinusOne_ne_one : icosianNormOneMinusOne≠1 := by
  intro h
  have he := congrArg (fun u : icosianNormOneGroup => u.val.val.re.re) h
  change (-1 : ℚ)=1 at he
  norm_num at he

theorem icosianNormOneReduction_minus_one :
    icosianNormOneReduction icosianNormOneMinusOne=1 := by
  apply Subtype.ext
  change icosianModuloTwo (-1 : icosianOrder)=1
  rw [map_neg,map_one]
  funext i j
  fin_cases i <;> fin_cases j <;> ext <;> simp

attribute [local instance] Classical.propDecidable

def icosianNormOneKernelEquiv : icosianNormOneReduction.ker ≃ Bool where
  toFun u := if u.val=1 then false else true
  invFun b := if b then ⟨icosianNormOneMinusOne,icosianNormOneReduction_minus_one⟩ else 1
  left_inv u := by
    apply Subtype.ext
    by_cases h : u.val=1
    · simp [h]
    · have hv := icosianNormOneReduction_kernel_values u.val u.property
      have he : u.val=icosianNormOneMinusOne := by
        apply icosianNormOne_value_injective
        rcases hv with hv | hv
        · exact False.elim (h (icosianNormOne_value_injective hv))
        · exact hv
      simp [he,icosianNormOneMinusOne_ne_one]
  right_inv b := by
    cases b <;> simp [icosianNormOneMinusOne_ne_one]

theorem icosianNormOneReduction_kernel_card : Nat.card icosianNormOneReduction.ker=2 := by
  rw [Nat.card_congr icosianNormOneKernelEquiv]
  simp

end Atlas.Algebra
