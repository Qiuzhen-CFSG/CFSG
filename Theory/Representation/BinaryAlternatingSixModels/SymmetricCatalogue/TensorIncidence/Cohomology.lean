module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.TensorIncidence.FlagVectors

/-!
# The building cohomology maps onto the tensor

Send a duad–syntheme flag to the pure tensor of its two endpoint vectors.
The endpoint sum relations kill every vertex coboundary, so this explicit
S₆-equivariant map descends to the literal top cohomology quotient. Its value
on each flag class is a nonzero pure tensor. Irreducibility of the alternating
tensor, the permitted hypothesis, implies surjectivity for S₆. Equality of the
proved dimensions then makes this particular map an equivariant equivalence.

Source: Aschbacher–Smith G.5.1, printed pp.342–343 (PDF pp.353–354).
This proves the tensor/incidence comparison conditional on alternating tensor
irreducibility; that irreducibility is retained for the source assembly owner.
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
open scoped TensorProduct
namespace BinaryAlternatingSix.SymmetricCatalogue

private noncomputable def flagTensor (f : Flag) : TensorModule :=
  (polarVector f.val.1).val ⊗ₜ[ZMod 2] lineVector f.val.2

private theorem flagTensor_action (g : S6) (f : Flag) :
    flagTensor (g • f) = tensorAction g (flagTensor f) := by
  change _ = firstNatural g (polarVector f.val.1).val ⊗ₜ[ZMod 2]
    secondNatural g (lineVector f.val.2)
  simp only [flagTensor, flag_smul_point, flag_smul_line, lineVector_action]
  rw [show firstNatural g (polarVector f.val.1).val =
    (polarVector (g • f.val.1)).val from polarAction_vector g f.val.1]

private noncomputable def flagTensorLinear : FlagModule →ₗ[ZMod 2] TensorModule where
  toFun v := ∑ f : Flag, v f • flagTensor f
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [mul_smul, Finset.smul_sum]

@[simp] private theorem flagTensorLinear_single (f : Flag) :
    flagTensorLinear (Pi.single f 1) = flagTensor f := by
  classical
  simp [flagTensorLinear]

private theorem flagTensorLinear_equivariant (g : S6) (v : FlagModule) :
    flagTensorLinear (flagRepresentation g v) = tensorAction g (flagTensorLinear v) := by
  change (∑ f : Flag, v (g⁻¹ • f) • flagTensor f) =
    tensorAction g (∑ f : Flag, v f • flagTensor f)
  rw [map_sum]
  simp only [map_smul, ← flagTensor_action]
  exact (Equiv.sum_comp (MulAction.toPerm g)
    (fun f : Flag => v (g⁻¹ • f) • flagTensor f)).symm.trans (by simp)

private noncomputable def flagTensorMap : flagRepresentation.IntertwiningMap tensorAction where
  toLinearMap := flagTensorLinear
  isIntertwining' g := LinearMap.ext (flagTensorLinear_equivariant g)

private theorem sum_flags (F : Duad → Syntheme → TensorModule) :
    (∑ f : Flag, F f.val.1 f.val.2) =
      ∑ d : Duad, ∑ s : Syntheme, if incident d s then F d s else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Duad × Syntheme =>
    if incident p.1 p.2 then F p.1 p.2 else 0)]
  apply Fintype.sum_of_injective (fun f : Flag => f.val) Subtype.val_injective
  · intro p hp
    have hn : ¬ incident p.1 p.2 := fun h => hp ⟨⟨p, h⟩, rfl⟩
    simp [hn]
  · intro f
    simp [f.property]

private theorem flagTensorMap_coboundary (v : VertexModule) : flagTensorMap (coboundary v) = 0 := by
  change (∑ f : Flag, (v.1 f.val.1 + v.2 f.val.2) • flagTensor f) = 0
  simp only [add_smul, Finset.sum_add_distrib, flagTensor]
  rw [sum_flags (fun d s => v.1 d • ((polarVector d).val ⊗ₜ[ZMod 2] lineVector s)),
    sum_flags (fun d s => v.2 s • ((polarVector d).val ⊗ₜ[ZMod 2] lineVector s))]
  have hp (d : Duad) :
      (∑ s : Syntheme, if incident d s then
        v.1 d • ((polarVector d).val ⊗ₜ[ZMod 2] lineVector s) else 0) = 0 := by
    calc
      _ = v.1 d • ((polarVector d).val ⊗ₜ[ZMod 2]
          (∑ s : Syntheme, if incident d s then lineVector s else 0)) := by
        rw [TensorProduct.tmul_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro s _
        split_ifs <;> simp
      _ = 0 := by rw [line_point_sum]; simp
  have hl (s : Syntheme) :
      (∑ d : Duad, if incident d s then
        v.2 s • ((polarVector d).val ⊗ₜ[ZMod 2] lineVector s) else 0) = 0 := by
    calc
      _ = v.2 s • ((∑ d : Duad, if incident d s then (polarVector d).val else 0)
          ⊗ₜ[ZMod 2] lineVector s) := by
        rw [TensorProduct.sum_tmul, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp
      _ = 0 := by rw [point_line_sum]; simp
  simp_rw [hp]
  rw [Finset.sum_comm]
  simp only [hl, Finset.sum_const_zero, add_zero]

private theorem coboundaries_le_flagTensorLinear_ker :
    coboundaries.toSubmodule ≤ flagTensorLinear.ker := by
  rintro _ ⟨v, rfl⟩
  exact flagTensorMap_coboundary v

private noncomputable def cohomologyTensorLinear : TopCohomology →ₗ[ZMod 2] TensorModule :=
  coboundaries.toSubmodule.liftQ flagTensorLinear coboundaries_le_flagTensorLinear_ker

private theorem cohomologyTensorLinear_mk (v : FlagModule) :
    cohomologyTensorLinear (coboundaries.toSubmodule.mkQ v) = flagTensorLinear v := rfl

/-- The flag tensor sum, descended through the actual coboundary quotient. -/
noncomputable def cohomologyTensorMap :
    topCohomologyRepresentation.IntertwiningMap tensorAction where
  toLinearMap := cohomologyTensorLinear
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := coboundaries.toSubmodule.mkQ_surjective x
    simp only [LinearMap.comp_apply]
    have hact : topCohomologyRepresentation g (coboundaries.toSubmodule.mkQ v) =
        coboundaries.toSubmodule.mkQ (flagRepresentation g v) :=
      coboundaries.quotientRepresentation_mk g v
    rw [hact, cohomologyTensorLinear_mk, cohomologyTensorLinear_mk]
    exact flagTensorLinear_equivariant g v

private theorem cohomologyTensorMap_mk_linear (v : FlagModule) :
    cohomologyTensorMap (coboundaries.toSubmodule.mkQ v) = flagTensorLinear v := rfl

private theorem pureTensor_ne_zero (v w : NaturalModule) (hv : v ≠ 0) (hw : w ≠ 0) :
    v ⊗ₜ[ZMod 2] w ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, polarForm a v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (polarForm_nondegenerate.2 v h)
  obtain ⟨b, hb⟩ : ∃ b, polarForm b w ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (polarForm_nondegenerate.2 w h)
  intro he
  have hh := congrArg (TensorProduct.dualDistrib (ZMod 2) NaturalModule NaturalModule
    (polarForm a ⊗ₜ[ZMod 2] polarForm b)) he
  rw [TensorProduct.dualDistrib_apply, map_zero] at hh
  exact mul_ne_zero ha hb hh

theorem cohomologyTensorMap_ne_zero : cohomologyTensorMap ≠ 0 := by
  intro he
  have hh := congrArg (fun f : topCohomologyRepresentation.IntertwiningMap tensorAction =>
    f (coboundaries.toSubmodule.mkQ (Pi.single baseFlag 1))) he
  simp only [cohomologyTensorMap_mk_linear, flagTensorLinear_single,
    IntertwiningMap.coe_zero, Pi.zero_apply] at hh
  exact pureTensor_ne_zero _ _ (polarVector baseFlag.val.1).property
    (lineVector_ne_zero baseFlag.val.2) hh

/-- The explicit incidence-to-tensor map is an isomorphism under the permitted
alternating irreducibility hypothesis. -/
noncomputable def cohomologyTensorEquiv (hTensor : IsIrreducible alternatingTensor) :
    topCohomologyRepresentation.Equiv tensorAction := by
  let := tensor_irreducible_of_alternating hTensor
  have hs := (IsIrreducible.surjective_or_eq_zero cohomologyTensorMap).resolve_right
    cohomologyTensorMap_ne_zero
  exact cohomologyTensorMap.ofBijective
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (topCohomology_finrank.trans tensor_finrank.symm)).mpr hs, hs⟩

/-- Formula on arbitrary cochain representatives. -/
theorem cohomologyTensorMap_mk (v : FlagModule) :
    cohomologyTensorMap (coboundaries.toSubmodule.mkQ v) =
      ∑ f : Flag, v f • ((polarVector f.val.1).val ⊗ₜ[ZMod 2] lineVector f.val.2) :=
  cohomologyTensorMap_mk_linear v

/-- A flag class maps to the pure tensor of its two marked endpoint vectors. -/
@[simp] theorem cohomologyTensorMap_flag (f : Flag) :
    cohomologyTensorMap (coboundaries.toSubmodule.mkQ (Pi.single f 1)) =
      (polarVector f.val.1).val ⊗ₜ[ZMod 2] lineVector f.val.2 :=
  flagTensorLinear_single f

@[simp] theorem cohomologyTensorEquiv_flag
    (hTensor : IsIrreducible alternatingTensor) (f : Flag) :
    cohomologyTensorEquiv hTensor (coboundaries.toSubmodule.mkQ (Pi.single f 1)) =
      (polarVector f.val.1).val ⊗ₜ[ZMod 2] lineVector f.val.2 := by
  change cohomologyTensorMap (coboundaries.toSubmodule.mkQ (Pi.single f 1)) = _
  exact cohomologyTensorMap_flag f

end BinaryAlternatingSix.SymmetricCatalogue
