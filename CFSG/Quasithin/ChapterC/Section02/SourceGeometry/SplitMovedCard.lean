module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.ElementaryAbelian.Injective
/-!
# Cardinality of the original split moved subgroup

A splitting of the actual B.5 moved section removes its central quotient
kernel. The literal quotient-action displacement coordinates then identify
the moved space with [V*,K], so dimension n gives subgroup order 2^n.
The comparison retains the original subgroup and action maps.

Source: Aschbacher–Smith B.5.1 and C.2.7, pp.99–103 and145–147.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem moved_central_eq_bot
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} {C : Subgroup D}
    (s : MovedSection ρ C) (hc : IsCompl s.space.toSubmodule (fixedSpace ρ C)) :
    s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact (disjoint_iff.mp hc.disjoint).le
    ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩

/-- The dimension of the literal split moved section determines the order of
its original commutator subgroup. -/
theorem star_moved_commutator_card
    (L R : Subgroup G) :
    let C := starImage L R L
    let J := offenderSubgroup (starRepresentation L R)
    ∀ (_hCJ : C ≤ J)
      (s : MovedSection ((starRepresentation L R).comp J.subtype) (C.subgroupOf J))
      (_hc : IsCompl s.space.toSubmodule
        (fixedSpace ((starRepresentation L R).comp J.subtype) (C.subgroupOf J)))
      (n : ℕ),
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = n →
      Nat.card (⁅starV L R, L.subgroupOf (L ⊔ R)⁆ : Subgroup (L ⊔ R : Subgroup G)) = 2 ^ n := by
  intro C J hCJ s hc n hn
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
  let b := s.central.toSubmodule.quotEquivOfEqBot (moved_central_eq_bot s hc)
  have hd : Module.finrank (ZMod 2) (Additive (⁅U,K⁆ : Subgroup (L ⊔ R : Subgroup G))) = n :=
    a.finrank_eq.trans (b.finrank_eq.symm.trans hn)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (⁅U,K⁆ : Subgroup (L ⊔ R : Subgroup G)))
  rw [Nat.card_congr Additive.toMul, hd, show Nat.card (ZMod 2) = 2 by simp] at hh
  exact hh

end CFSG.Quasithin.ChapterC.C27Source
