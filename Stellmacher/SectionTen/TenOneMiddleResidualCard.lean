module
public import Stellmacher.SectionTen.TenOneMiddleCenterResidual
public import Stellmacher.SectionTen.TenOneMiddleResidualNeighborhood
public import Stellmacher.SectionTen.TenOneSmallNeighborhoodQuotientAction
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# The middle residual core has order sixteen

In the actual first-module order-eight, SL2(2) case of Section Ten, the
middle residual two-core has order sixteen.

Retain the literal neighborhood quotient action and its normality witness.
The actual residual image has displacement of order four on U/Zmiddle.
The quotient-conjugation image formula identifies this with the relative
index of Zmiddle in [U,Emiddle]. The proved residual equality identifies
that commutator as O₂(Emiddle). Its middle center has order four and is
contained in the residual core, so the exact index/cardinality formula
gives order sixteen.

Source: Stellmacher (10.1)(a1), printed p.60/PDF p.50, the middle residual
calculation before C4×C4 recognition, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_middle_residual_core_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    Nat.card (twoCoreIn (EAt ctx.Γ middle)) = 16 := by
  let M := GAt ctx.Γ middle
  let U := GeneratedNeighborhoodV ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let D := twoCoreIn E
  obtain ⟨hN,hMU,_,_,action,hact,_,_,_,hcard⟩ :=
    ten_one_small_neighborhood_quotient_action ctx middle hpath hsmall
  let _ := hN
  have hEM : E ≤ M := by
    change ctx.Γ.twoResidualAt middle ≤ M
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hindex : Z.relIndex D = 4 := by
    have hh := Subgroup.quotient_conjugation_commutatorAction_card M U Z E hMU hEM hN action hact
    rw [hcard] at hh
    change 4 = Z.relIndex ⁅U,E⁆ at hh
    rw [← ten_one_middle_residual_neighborhood ctx middle hpath hsmall hmodel] at hh
    exact hh.symm
  have hZD : Z ≤ D := ten_one_middle_center_le_residual_core ctx middle hpath
  have hcount := (Z.subgroupOf D).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv,
    show Nat.card Z = 4 from (sectionTenOpeningData ctx middle hpath).center_card] at hcount
  change Z.relIndex D * 4 = Nat.card D at hcount
  rw [hindex] at hcount
  exact hcount.symm
end Stellmacher.SectionTen
