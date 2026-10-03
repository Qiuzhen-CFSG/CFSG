module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Stellmacher.Recognition.LargeTerminalFiveCentralizer
public import Stellmacher.Recognition.LargeTerminalFiveLocalAutomorphisms
public import Theory.GroupTheory.NormalizerCentralizerLift

/-!
# Confinement of the large terminal five-normalizer

The second local quotient is the faithful C₅ ⋊ C₄ group, and its normalizer
action on the specified five-subgroup realizes all automorphisms. Match an
ambient normalizer element with a local element inducing the same automorphism;
their quotient lies in the five-centralizer, which is confined to the second
local group in the noncyclic four-fixed alternative.

The conditional reduction remains available, and the final theorem discharges
both local surjectivity and centralizer confinement. It uses no ambient
Sylow-five assertion or odd-local solvability.

Source: Thompson VI, printed p.630, the five-normalizer assertion in the
noncyclic four-fixed alternative.
-/

namespace Stellmacher.Recognition

open SectionsFiveToSeven Subgroup

universe u

/-- Realizing all automorphisms locally makes the two confinement assertions
equivalent for the specified ambient subgroup. -/
public theorem LargeTerminalContext.normalizer_le_second_iff_centralizer_le_of_surjective
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hAut : Function.Surjective (A.normalizerMonoidHom.comp
      (ctx.second.subgroupOf (normalizer (A : Set G))).subtype)) :
    normalizer (A : Set G) ≤ ctx.second ↔ centralizer (A : Set G) ≤ ctx.second :=
  ⟨fun h => (Subgroup.centralizer_le_normalizer _).trans h,
    fun h => normalizer_le_of_centralizer_le_of_surjective A ctx.second h hAut⟩

/-- The actual five-normalizer lies in the second local subgroup in the
noncyclic four-fixed alternative at Sylow order 4096. -/
public theorem LargeTerminalContext.five_normalizer_le_second
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
    normalizer (A : Set G) ≤ ctx.second :=
  (ctx.normalizer_le_second_iff_centralizer_le_of_surjective A
    (ctx.five_local_automorphisms_surjective hS A hA hAP)).mpr
      (ctx.five_centralizer_le_second hS A hA hAP hAN hcard hncyc hfixed)

end Stellmacher.Recognition
