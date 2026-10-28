module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.IntrinsicIrreducible
/-!
# Irreducibility through the original conjugation image

A surjection of actors and an injective realization of an Irr⁺ binary module
as U(L) transport the full invariant normal-subgroup interval to L. Fixed
vectors become exactly U(L) ∩ Z(L); no central layer is removed.
Source: Aschbacher–Smith C.1.7 and the moved-module argument in C.5.13, p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC
variable {L H W : Type*} [Group L] [Group H] [AddCommGroup W] [Module (ZMod 2) W]

theorem blockModuleIrreducible_of_isIrrPlus_image
    (ρ : Representation (ZMod 2) H W) (f : L →* H) (hf : Function.Surjective f)
    (j : Multiplicative W →* L) (hj : Function.Injective j) (hr : j.range = blockU L)
    (he : ∀ l w, j (Multiplicative.ofAdd (ρ (f l) w)) = l * j (Multiplicative.ofAdd w) * l⁻¹)
    (hi : IsIrrPlus ρ ⊤ ⊤) : BlockModuleIrreducible L := by
  have hfixed (w : W) : w ∈ fixedSpace ρ ⊤ ↔ j (Multiplicative.ofAdd w) ∈ center L := by
    constructor
    · intro hw
      rw [mem_center_iff]
      intro l
      have hh := congrArg (fun v : W => j (Multiplicative.ofAdd v)) (hw ⟨f l,mem_top _⟩)
      change j (Multiplicative.ofAdd (ρ (f l) w)) = j (Multiplicative.ofAdd w) at hh
      rw [he] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hw a
      obtain ⟨l,hl⟩ := hf a.val
      apply Multiplicative.ofAdd.injective
      apply hj
      change j (Multiplicative.ofAdd (ρ a.val w)) = j (Multiplicative.ofAdd w)
      rw [← hl,he,mem_center_iff.mp hw l,mul_inv_cancel_right]
  refine ⟨lt_of_le_of_ne inf_le_left ?_,?_⟩
  · intro hh
    apply hi.not_le_fixedSpace ρ
    intro w _
    apply (hfixed w).mpr
    exact (hh.ge (hr ▸ show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩)).2
  · intro A hA hlo hhi
    let J : Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2 (A.comap j).toAddSubgroup'
    have hJ : (⊤ : Subgroup H) ≤ subspaceStabilizer ρ J := by
      apply le_subspaceStabilizer
      intro a _ w hw
      obtain ⟨l,rfl⟩ := hf a
      change j (Multiplicative.ofAdd (ρ (f l) w)) ∈ A
      rw [he]
      exact hA.conj_mem _ hw l
    rcases hi.eq_or_le_fixedSpace ρ hJ le_top with htop | hfix
    · right
      apply le_antisymm hhi
      intro a ha
      obtain ⟨w,rfl⟩ := (show a ∈ j.range from hr.symm ▸ ha)
      exact (show w.toAdd ∈ J from htop ▸ Submodule.mem_top)
    · left
      apply le_antisymm _ hlo
      intro a ha
      refine ⟨hhi ha,?_⟩
      obtain ⟨w,rfl⟩ := (show a ∈ j.range from hr.symm ▸ hhi ha)
      exact (hfixed w.toAdd).mp (hfix ha)
end CFSG.Quasithin.ChapterC
