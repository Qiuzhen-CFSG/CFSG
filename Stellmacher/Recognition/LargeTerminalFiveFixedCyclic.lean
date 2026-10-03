module

public import Stellmacher.Recognition.LargeTerminalFiveFixedInvolution
public import Stellmacher.Recognition.LargeTerminalFourFixedFusion
public import Stellmacher.Recognition.LargeTerminalFourFixedOddLocal

/-!
# Cyclicity of the actual order-four five-fixed subgroup

The original order-five witness retains its local containment, normalization,
fixed order, and fixed-center property. The noncyclic case supplies an
involution outside the first residual. Fusion either conjugates this involution
to the omega-central involution or makes its centralizer order divisible by
fifteen. The odd-local exclusions rule out both alternatives, proving cyclicity
with the actual ambient embeddings and fixed-center property unchanged.

Source: Thompson VI, printed pp.629--630.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- The saved order-five witness either has cyclic fixed subgroup or supplies
an actual involution to which the remaining global exclusion must apply. -/
public theorem LargeTerminalContext.exists_five_fixed_cyclic_or_involution_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ A : Subgroup G, Nat.card A = 5 ∧ A ≤ ctx.second ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4 ∧
      (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤ center ctx.firstResidual ∧
      (IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) ∨
        ∃ y : G, y ∈ twoCoreIn ctx.second ∧ y ∈ centralizer (A : Set G) ∧
          y ∉ ctx.firstResidual ∧ orderOf y = 2) := by
  classical
  obtain ⟨A, hA, hAP, hAN, hcard, hfixed⟩ := ctx.exists_five_fixed_four_of_large_card hS
  refine ⟨A, hA, hAP, hAN, hcard, hfixed, ?_⟩
  by_cases hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second))
  · exact Or.inl hcyc
  · exact Or.inr (ctx.exists_five_fixed_involution_of_not_cyclic A hcard hfixed hcyc)

/-- The actual order-four fixed subgroup is cyclic: the noncyclic alternative
contradicts the fusion and odd-local conclusions of the terminal context. -/
public theorem LargeTerminalContext.five_fixed_isCyclic_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual) :
    IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) := by
  classical
  by_contra hncyc
  obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
  obtain ⟨y, hyQ, hyA, hyR, hy2, hdisj⟩ :=
    ctx.exists_five_fixed_fusion_of_not_cyclic hS A hA hAN hcard hfixed hncyc z hz hgen
  obtain ⟨hnconj, hn15⟩ := ctx.noncyclic_four_fixed_involution_exclusions
    hS A hA hAP hAN hcard hncyc hfixed z hz hgen y hyQ hyA hyR hy2
  exact hdisj.elim hnconj hn15

/-- At the order-4096 endpoint, an actual order-five subgroup fixes a cyclic
subgroup of order four in the second core and only central elements in the
first residual. -/
public theorem LargeTerminalContext.exists_five_fixed_cyclic_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ A : Subgroup G, Nat.card A = 5 ∧ A ≤ ctx.second ∧
      A ≤ normalizer (ctx.firstResidual : Set G) ∧
      Nat.card ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) = 4 ∧
      (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤ center ctx.firstResidual ∧
      IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)) := by
  obtain ⟨A, hA, hAP, hAN, hcard, hfixed⟩ := ctx.exists_five_fixed_four_of_large_card hS
  exact ⟨A, hA, hAP, hAN, hcard, hfixed,
    ctx.five_fixed_isCyclic_of_large_card hS A hA hAP hAN hcard hfixed⟩

end Stellmacher.Recognition
