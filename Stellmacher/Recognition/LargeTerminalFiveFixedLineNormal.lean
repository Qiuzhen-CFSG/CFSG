module

public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Stellmacher.Recognition.LargeTerminalFiveFixedFourNormal

/-!
# The distinguished line in the actual five-centralizer

At the upper endpoint the residual normalizer is exactly the second local
subgroup, by the full involution-centralizer theorem. Global line normality
follows from invariance of the actual fixed
four-group under the five-centralizer and confinement of that four-group's
normalizer. The latter is a two-local problem: the ambient fixed-group data
in `LargeTerminalFourFixedLocalData` supplies solvability and characteristic
two for its normalizer.

The conditional assembly keeps both assertions explicit. The final theorem
discharges them using the fixed-four invariance and normalizer-confinement
theorems. Thus every element of the five-centralizer fixes the distinguished
involution, which makes its generated line normal.

Source: Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable, VI*, printed p.630, the five-normalizer assertion in the noncyclic
four-fixed alternative. We retain the N₂ setting and do not assume solvability
of odd-local subgroups or ambient Sylow-five status.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- The full residual normalizer is the second local group at the upper endpoint. -/
public theorem LargeTerminalContext.residual_normalizer_eq_second_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    normalizer (ctx.firstResidual : Set G) = ctx.second := by
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  apply le_antisymm _ ctx.second_le_residual_normalizer
  exact (ctx.residual_normalizer_le_involution_centralizer z hz hgen).trans_eq
    (ctx.involution_centralizer_eq_second hS z hz hgen)

/-- Invariance of the actual fixed four-group and control of its normalizer
suffice to make the distinguished line normal in the full five-centralizer. -/
public theorem LargeTerminalContext.five_fixed_line_normal_of_four_normalizer_control
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hFnormal : ((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
      (centralizer (A : Set G))).Normal)
    (hNF : normalizer (twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Set G) ≤
      ctx.second) :
    ((omegaOneCenter (S : Subgroup G)).subgroupOf (centralizer (A : Set G))).Normal := by
  have hCF := (normal_subgroupOf_iff_le_normalizer
    (show twoCoreIn ctx.second ⊓ centralizer (A : Set G) ≤
      centralizer (A : Set G) from inf_le_right)).mp hFnormal
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  have hCz : centralizer (A : Set G) ≤ centralizer ({z} : Set G) :=
    hCF.trans (hNF.trans (ctx.second_le_residual_normalizer.trans
      (ctx.residual_normalizer_le_involution_centralizer z hz hgen)))
  rw [← centralizer_closure ({z} : Set G), ← zpowers_eq_closure, hgen] at hCz
  exact normal_subgroupOf_of_le_normalizer
    (hCz.trans (Subgroup.centralizer_le_normalizer _))

/-- The distinguished order-two line is normal in the full five-centralizer
in the noncyclic four-fixed alternative. -/
public theorem LargeTerminalContext.five_fixed_line_normal
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    ((omegaOneCenter (S : Subgroup G)).subgroupOf (centralizer (A : Set G))).Normal := by
  exact ctx.five_fixed_line_normal_of_four_normalizer_control A
    (ctx.five_fixed_four_normal hS A hA hAP hAN hcard hncyc hfixed)
    (ctx.five_fixed_four_normalizer_le_second hS A hA hAP hAN hcard hncyc hfixed)

end Stellmacher.Recognition
