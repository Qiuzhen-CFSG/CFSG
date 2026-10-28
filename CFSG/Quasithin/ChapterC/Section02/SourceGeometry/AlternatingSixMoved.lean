module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SplitMovedCard
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.AlternatingSixMovedCover

/-!
# The order of the original natural-A₆ moved subgroup

The actual B.5 moved space lies between its four-dimensional natural quotient
and the universal five-dimensional augmentation cover. The literal star-action
coordinates identify this space with [V*,K], giving order 16 or 32 without
assuming that its central quotient splits.

Source: Aschbacher–Smith B.5.1 and C.2.7, pp.99–103 and145–147; the original
14.6.10(5) consumer on p.1029 uses the resulting rank bound.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The literal natural-A₆ commutator module has order 16 or 32. -/
theorem star_alternatingSix_moved_card
    (L R : Subgroup G) :
    let C := starImage L R L
    let J := offenderSubgroup (starRepresentation L R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation L R).comp J.subtype) (C.subgroupOf J))
      (_hi : IsIrrPlus ((starRepresentation L R).comp J.subtype)
        (C.subgroupOf J) s.space.toSubmodule)
      (_e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) (alternatingNatural 6)),
      Nat.card (⁅starV L R, L.subgroupOf (L ⊔ R)⁆ : Subgroup (L ⊔ R : Subgroup G)) = 16 ∨
      Nat.card (⁅starV L R, L.subgroupOf (L ⊔ R)⁆ : Subgroup (L ⊔ R : Subgroup G)) = 32 := by
  intro C J hCJ s hi e
  let U := starV L R
  let K := L.subgroupOf (L ⊔ R)
  let : IsElementaryAbelian 2 (⁅U,K⁆ : Subgroup (L ⊔ R : Subgroup G)) :=
    IsElementaryAbelian.of_injective (inclusion (commutator_le_left U K))
      (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel L R)
  have hs : s.space.toSubmodule =
      subspaceCommutator (starRepresentation L R) ⊤ (K.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation L R).comp J.subtype) ⊤
      (C.subgroupOf J) = _
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hCJ]
    rfl
  let a : Additive (⁅U,K⁆ : Subgroup (L ⊔ R : Subgroup G)) ≃ₗ[ZMod 2]
      s.space.toSubmodule :=
    (NormalElementaryQuotient.movedEquiv U q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) K).trans (LinearEquiv.ofEq _ _ hs.symm)
  have hhi := s.alternatingSix_finrank_le_five hi e
  have hlo := s.central.toSubmodule.finrank_quotient_le
  have he := e.linearEquiv.finrank_eq
  rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at he
  norm_num only [Fintype.card_fin] at he
  rw [he] at hlo
  have hn : Module.finrank (ZMod 2) s.space.toSubmodule = 4 ∨
      Module.finrank (ZMod 2) s.space.toSubmodule = 5 := by omega
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (⁅U,K⁆ : Subgroup (L ⊔ R : Subgroup G)))
  rw [Nat.card_congr Additive.toMul, a.finrank_eq, Nat.card_zmod] at hh
  rcases hn with hn | hn
  · left
    norm_num [hn] at hh
    exact hh
  · right
    norm_num [hn] at hh
    exact hh
end CFSG.Quasithin.ChapterC.C27Source
