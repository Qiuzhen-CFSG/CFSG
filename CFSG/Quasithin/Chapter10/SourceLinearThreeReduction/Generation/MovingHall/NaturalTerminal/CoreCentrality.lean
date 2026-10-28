module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CoreQuotient
public import Theory.GroupTheory.CComponent.LocalFaithfulCore
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Quasisimplicity of the actual common overcomponent

The original block embeds faithfully modulo the common component's two-core
and remains a local C-component for its literal Sylow intersection. Local
component calculus therefore makes the two-core central. The perfect central
cover of the already quasisimple quotient is quasisimple itself.

This removes the nonquasisimple overcomponent case from the literal moving
Hall consumer. Recognition and triviality of the two-core, natural marking,
and Hall placement remain with qt-d-10-nona5-moving-hall-three.
Source: Aschbacher–Smith 10.2.3(4), printed p.747, and A.3.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Faithfulness on a local natural block forces the common component's
entire two-core to be central. -/
theorem CommonOvercomponent.twoCore_le_center
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) : pCore 2 c.overcomponent ≤ center c.overcomponent := by
  have hC : (⊤ : Subgroup c.overcomponent).IsCComponent := by
    simpa only [subgroupOf_self] using c.component.2.subgroupOf_of_le le_rfl c.component.1
  obtain ⟨P,_,hJ,_⟩ := c.local_family
  apply twoCore_le_center_of_faithful_local_component hC P (c.original.subgroupOf c.overcomponent) hJ
  intro x y he
  have hx := hi (a₁ := (subgroupOfEquivOfLe c.original_lt.le) x)
    (a₂ := (subgroupOfEquivOfLe c.original_lt.le) y) he
  exact (subgroupOfEquivOfLe c.original_lt.le).injective hx

/-- The literal common component, not just its two-core quotient, is quasisimple. -/
theorem CommonOvercomponent.quasisimple
    {H : Subgroup G} {B : Subgroup H} {n : ℕ}
    (c : CommonOvercomponent T L H B n)
    (hi : Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
      (inclusion c.original_lt.le))) : IsQuasisimple c.overcomponent := by
  let C := c.overcomponent
  let : IsQuasisimple (C ⧸ pCore 2 C) := (c.quotient_rank_and_quasisimple hi).2
  have hC : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using c.component.2.subgroupOf_of_le le_rfl c.component.1
  let : Group.IsPerfect (⊤ : Subgroup C) := hC.perfect
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := C)).toMonoidHom) (topEquiv (G := C)).surjective
  exact (show PerfectCentralCovering.Cover C (C ⧸ pCore 2 C) from {
    toMonoidHom := QuotientGroup.mk' (pCore 2 C)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := by simpa only [QuotientGroup.ker_mk'] using c.twoCore_le_center hi }).isQuasisimple

end CFSG.Quasithin.Chapter10.MovingHall
