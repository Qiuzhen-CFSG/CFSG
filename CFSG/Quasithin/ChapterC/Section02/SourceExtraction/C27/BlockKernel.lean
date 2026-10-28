module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Omega
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Quotients

/-!
# Faithfulness of the core-to-star map for a block

The intrinsic block layer U(X) lies in the central omega subgroup of XR.
An element of X in the star kernel therefore centralizes U(X), so lies in
O₂(X). Consequently the literal map X/O₂(X) to X* is injective. This
retains the original radical and quotient, including any central-cover
possibility before the block hypothesis is established.

Source: Aschbacher--Smith C.1.7--11 and C.2.7, pp.123--124 and 145--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {X R : Subgroup G}

/-- A block loses no additional central kernel under the original star map. -/
theorem coreToStar_injective_of_block
    (hn : R ≤ normalizer (X : Set G))
    (hb : ChapterC.IsBlock (X.subgroupOf (X ⊔ R))) :
    Function.Injective (coreToStar hn) := by
  let D := X ⊔ R
  let L := X.subgroupOf D
  let a : L ≃* X := subgroupOfEquivOfLe (show X ≤ D from le_sup_left)
  have hk : (toStarImage X R).ker ≤ pCore 2 X := by
    intro x hx
    let y : L := a.symm x
    have hy : (y : D) ∈ starKernel X R := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hx
    have hyc : y ∈ centralizer (ChapterC.blockU L : Set L) := by
      intro u hu
      apply Subtype.ext
      exact hy u (ChapterC.BlockOmega.layer_le_omega hb (mem_map_of_mem L.subtype hu))
    have hyp := hb.short.centralizer_blockU.le hyc
    have hh := mem_map_of_mem a.toMonoidHom hyp
    rw [pCore_map_iso 2 a] at hh
    change a (a.symm x) ∈ pCore 2 X at hh
    rwa [a.apply_symm_apply] at hh
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) x
  exact (QuotientGroup.eq_one_iff _).mpr (hk hx)

end CFSG.Quasithin.ChapterC.C27Source
