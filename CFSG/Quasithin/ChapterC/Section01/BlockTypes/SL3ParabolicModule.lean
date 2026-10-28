module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.SL3.ParabolicSubgroups

/-!
# Natural SL₃ block modules under a marked parabolic residual

The image of a nonzero commutator-generated subgroup in U/C_U(X) is again
nonzero and commutator-generated. The additive-subgroup calculation for the
actual vector/covector stabilizers makes this image absorb [U,A]. Taking the
preimage gives [U,A] ≤ W C_U(X), with the original quotient and conjugation
maps retained. This argument does not require splitting the central cover.

Source: Aschbacher--Smith C.4.7 and original 4.3.7, printed pp.153 and 616.
The rank-one application discharges the subgroup hypotheses; constructing its
parabolic residual marking remains with the block-exclusion assembly.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {X : Type*} [Group X] {F : Type*} [Field F]

/-- The actual central quotient of a natural SL₃ block absorbs all local
commutators as soon as the original local image is a parabolic residual. -/
theorem BlockModuleModel.sl3_commutator_le_fixed_sup
    {rho : SL(3,F) →* MulAut (Multiplicative (Fin 3 → F))}
    (m : BlockModuleModel X rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (A W : Subgroup X) (hWU : W ≤ blockU X) (hne : W ≠ ⊥)
    (hcomm : ⁅W,A⁆ = W)
    (hA : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
        Matrix.PSL3.LinearThree.pointLocalSL F ∨
      A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))) =
        Matrix.PSL3.LinearThree.lineLocalSL F) :
    ⁅blockU X,A⁆ ≤ W ⊔ (blockU X ⊓ center X) := by
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let q := m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed X))
  let Q := (W.subgroupOf (blockU X)).map q
  have hk : q.ker = blockFixed X := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.moduleIso.injective, QuotientGroup.ker_mk']
  have hq (a : X) (u : blockU X) :
      (q (blockConjugate X a u)).toAdd = (p a).val.mulVec (q u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' _ (blockConjugate X a u))).toAdd = _
    rw [m.intertwining, hrho]
    rfl
  have hd (a : X) (u : blockU X) :
      (q (blockConjugate X a u * u⁻¹)).toAdd =
        (p a).val.mulVec (q u).toAdd - (q u).toAdd := by
    rw [map_mul, map_inv]
    change (q (blockConjugate X a u)).toAdd + -(q u).toAdd = _
    rw [hq]
    exact (sub_eq_add_neg _ _).symm
  have hWn : A ≤ normalizer (W : Set X) := by
    rw [le_normalizer_iff_commutator_le_right, commutator_comm, hcomm]
  have hQ : ∀ g ∈ A.map p, ∀ v ∈ Q.toAddSubgroup', g.val.mulVec v ∈ Q.toAddSubgroup' := by
    rintro g ⟨a,ha,rfl⟩ v ⟨u,hu,huv⟩
    refine ⟨blockConjugate X a u, ?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hWn ha) (u : X)).mp hu
    · apply Multiplicative.toAdd.injective
      rw [hq, huv]
      rfl
  have hQne : Q.toAddSubgroup' ≠ ⊥ := by
    intro he
    have hWZ : W ≤ center X := by
      intro w hw
      let u : blockU X := ⟨w,hWU hw⟩
      have hmem : (q u).toAdd ∈ Q.toAddSubgroup' := ⟨u,hw,rfl⟩
      rw [he] at hmem
      have hu : u ∈ q.ker := hmem
      rw [hk] at hu
      exact hu
    have hc : ⁅W,A⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro w hw a _
      exact mem_center_iff.mp (hWZ hw) a
    exact hne (hcomm.symm.trans hc)
  have hmove : ∀ S : AddSubgroup (Fin 3 → F),
      (∀ g ∈ A.map p, ∀ v ∈ Q.toAddSubgroup', g.val.mulVec v - v ∈ S) →
        Q.toAddSubgroup' ≤ S := by
    intro S hS
    let M := (S.toSubgroup.comap q).map (blockU X).subtype
    have hc : ⁅A,W⁆ ≤ M := by
      apply commutator_le.mpr
      intro a ha w hw
      let u : blockU X := ⟨w,hWU hw⟩
      refine ⟨blockConjugate X a u * u⁻¹, ?_, rfl⟩
      change (q (blockConjugate X a u * u⁻¹)).toAdd ∈ S
      rw [hd]
      exact hS _ (mem_map_of_mem p ha) _ ⟨u,hw,rfl⟩
    rw [commutator_comm, hcomm] at hc
    rintro v ⟨u,hu,huv⟩
    obtain ⟨z,hz,hzu⟩ := hc hu
    have hzu : z = u := Subtype.ext hzu
    subst z
    change (q u).toAdd ∈ S at hz
    rw [huv] at hz
    exact hz
  have ht : (Q.comap q).map (blockU X).subtype = W ⊔ (blockU X ⊓ center X) := by
    rw [Subgroup.comap_map_eq, Subgroup.map_sup, hk,
      map_subgroupOf_eq_of_le hWU, blockFixed_map]
  rw [commutator_comm, ← ht]
  apply commutator_le.mpr
  intro a ha u hu
  let v : blockU X := ⟨u,hu⟩
  refine ⟨blockConjugate X a v * v⁻¹, ?_, rfl⟩
  change (q (blockConjugate X a v * v⁻¹)).toAdd ∈ Q.toAddSubgroup'
  rw [hd]
  exact Representation.SL3ParabolicNatural.displacement_mem_of_moved
    (A.map p) hA Q.toAddSubgroup' hQne hQ hmove _ (mem_map_of_mem p ha) _
end CFSG.Quasithin.ChapterC
