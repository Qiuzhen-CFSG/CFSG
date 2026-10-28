/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialKernel.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialReduction

/-!
# IcosianMonomialKernel

The kernel of monomial reduction consists of three independent scalar kernels. Its
cardinality and the finite glue stabilizer determine the lifted group order.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialKernel.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes
attribute [local irreducible] icosianGlueMonomialStabilizer icosianNormOneReduction

theorem icosianMonomialReduction_kernel_iff (g : IcosianUnitMonomial) :
    icosianMonomialReduction g=1 ↔
      (∀ i,icosianNormOneReduction (g.left i)=1) ∧ g.right=1 := by
  constructor
  · intro h
    exact ⟨fun i => congrFun (congrArg SemidirectProduct.left h) i,
      congrArg SemidirectProduct.right h⟩
  · rintro ⟨hl,hr⟩
    apply SemidirectProduct.ext
    · exact funext hl
    · exact hr

def icosianMonomialKernelEquiv :
    icosianLiftedMonomialProjection.ker ≃ (Fin 3 → icosianNormOneReduction.ker) where
  toFun g i := ⟨g.val.val.left i,
    ((icosianMonomialReduction_kernel_iff g.val.val).mp
      (congrArg Subtype.val g.property)).1 i⟩
  invFun u := ⟨⟨⟨fun i => (u i).val,1⟩,by
    change icosianMonomialReduction ⟨fun i => (u i).val,1⟩ ∈
      icosianGlueMonomialStabilizer GoldenFour
    rw [(icosianMonomialReduction_kernel_iff ⟨fun i => (u i).val,1⟩).mpr ⟨fun i => (u i).property,rfl⟩]
    exact (icosianGlueMonomialStabilizer GoldenFour).one_mem⟩,by
      apply Subtype.ext
      exact (icosianMonomialReduction_kernel_iff ⟨fun i => (u i).val,1⟩).mpr ⟨fun i => (u i).property,rfl⟩⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact ((icosianMonomialReduction_kernel_iff g.val.val).mp
        (congrArg Subtype.val g.property)).2.symm
  right_inv u := by funext i; rfl

theorem icosianLiftedMonomialProjection_kernel_card :
    Nat.card icosianLiftedMonomialProjection.ker=8 := by
  rw [Nat.card_congr icosianMonomialKernelEquiv,Nat.card_fun,
    icosianNormOneReduction_kernel_card]
  norm_num

theorem icosianLiftedMonomial_card : Nat.card icosianLiftedMonomial=2304 := by
  have h := icosianLiftedMonomialProjection.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    icosianLiftedMonomialProjection icosianLiftedMonomialProjection_surjective).toEquiv,
    icosianLiftedMonomialProjection_kernel_card,
    icosianGlueMonomialStabilizer_card_four (F := GoldenFour)
      (by rw [Nat.card_eq_fintype_card,goldenFour_card])] at h
  exact h.trans (by norm_num)

end Atlas.Conway
