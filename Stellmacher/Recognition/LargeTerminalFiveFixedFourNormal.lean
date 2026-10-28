module

public import Stellmacher.Recognition.LargeTerminalFiveFixedFourOddComplement

/-!
# Normality of the actual fixed four-group

The actual fixed group V = C_Q(A) is Sylow in C_G(A), and Burnside
transfer supplies a normal odd complement K. The involution-centralizer
core argument shows that K centralizes V. Together these facts make V
normal in the full five-centralizer.

The checked Sylow, transfer, and local-order results are re-exported from
LargeTerminalFiveFixedFourSylow through the odd-complement module.

Source: Thompson VI, printed p.630, the noncyclic four-fixed alternative.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven Subgroup

universe u

/-- Centralization by every normal odd complement finishes invariance of the
actual fixed four-group under the full five-centralizer. -/
public theorem LargeTerminalContext.five_fixed_four_normal_of_odd_complement_centralizes
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (hodd : ∀ K : Subgroup (centralizer (A : Set G)), K.Normal →
      Odd (Nat.card K) →
      K.IsComplement' ((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
        (centralizer (A : Set G))) →
      K ≤ centralizer (((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
        (centralizer (A : Set G))) : Set (centralizer (A : Set G)))) :
    ((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
      (centralizer (A : Set G))).Normal := by
  obtain ⟨K, hKnormal, hKodd, hKcomp⟩ :=
    ctx.five_centralizer_exists_normal_odd_complement hS A hA hAP hAN hcard hncyc hfixed
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hKcomp.sup_eq_top]
  exact sup_le ((hodd K hKnormal hKodd hKcomp).trans
    (Subgroup.centralizer_le_normalizer _)) le_normalizer

/-- The actual fixed four-group is invariant under the full five-centralizer. -/
public theorem LargeTerminalContext.five_fixed_four_normal
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
    ((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
      (centralizer (A : Set G))).Normal := by
  apply ctx.five_fixed_four_normal_of_odd_complement_centralizes
    hS A hA hAP hAN hcard hncyc hfixed
  intro K hKnormal hKodd hKcomp
  exact ctx.five_fixed_four_odd_complement_le_centralizer
    hS A hA hAP hAN hcard hncyc hfixed K hKnormal hKodd hKcomp

end Stellmacher.Recognition
