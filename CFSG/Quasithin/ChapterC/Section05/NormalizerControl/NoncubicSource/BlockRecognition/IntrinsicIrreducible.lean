module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# From Irr⁺ to the C.1.7 block interval

An Irr⁺ commutator module for the literal conjugation action has exactly the
central subgroup interval required by `BlockModuleIrreducible`: a proper
invariant normal subgroup is fixed by the actor, hence lies in the center.
The theorem retains an explicit binary-module instance so callers can install
`IsElementaryAbelian.isVectorSpace` locally.
Source: Aschbacher–Smith C.1.7 and A.1.40.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [IsMulCommutative (blockU L)]
variable [Module (ZMod 2) (Additive (blockU L))]

theorem blockModuleIrreducible_of_conjugation_isIrrPlus
    (ρ : Representation (ZMod 2) L (Additive (blockU L)))
    (he : ∀ l v, ρ l v = Additive.ofMul (blockConjugate L l v.toMul))
    (hi : IsIrrPlus ρ ⊤ ⊤) : BlockModuleIrreducible L := by
  have hf (v : Additive (blockU L)) :
      v ∈ fixedSpace ρ ⊤ ↔ (v.toMul : L) ∈ center L := by
    constructor
    · intro hv
      rw [mem_center_iff]
      intro l
      have hh' := congrArg id (hv ⟨l,mem_top l⟩)
      change ρ l v = v at hh'
      rw [he] at hh'
      have hh'' := congrArg (fun w : Additive (blockU L) => (w.toMul : L)) hh'
      change l * (v.toMul : L) * l⁻¹ = (v.toMul : L) at hh''
      exact mul_inv_eq_iff_eq_mul.mp hh''
    · intro hv l
      change ρ l.val v = v
      rw [he]
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : L) * (v.toMul : L) * (l : L)⁻¹ = (v.toMul : L)
      rw [mem_center_iff.mp hv l.val,mul_inv_cancel_right]
  refine ⟨lt_of_le_of_ne inf_le_left ?_,?_⟩
  · intro hh
    apply hi.not_le_fixedSpace ρ
    intro v hv
    apply (hf v).mpr
    exact (hh.ge v.toMul.property).2
  · intro N hN hlow hhigh
    let : N.Normal := hN
    let J : Submodule (ZMod 2) (Additive (blockU L)) :=
      AddSubgroup.toZModSubmodule 2 (N.subgroupOf (blockU L)).toAddSubgroup
    have hJ : (⊤ : Subgroup L) ≤ subspaceStabilizer ρ J := by
      apply le_subspaceStabilizer
      intro l hl v hv
      rw [he]
      exact hN.conj_mem _ hv l
    rcases hi.eq_or_le_fixedSpace ρ hJ le_top with hj | hj
    · right
      apply le_antisymm hhigh
      intro u hu
      have hm : Additive.ofMul (⟨u,hu⟩ : blockU L) ∈ J := hj ▸ Submodule.mem_top
      exact hm
    · left
      apply le_antisymm _ hlow
      intro u hu
      refine ⟨hhigh hu,?_⟩
      exact (hf (Additive.ofMul ⟨u,hhigh hu⟩)).mp (hj hu)
end CFSG.Quasithin.ChapterC
