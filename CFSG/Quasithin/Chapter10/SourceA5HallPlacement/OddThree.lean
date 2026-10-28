module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalCenter
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.OddThree

/-!
# Odd ternary exclusions in the original Hall normalizer

The original nonnormal component has trivial center and the proved additive
local plus ordinary rank budget. Transporting its literal central-quotient
model along that center equality applies both odd ternary exclusions without
any extra model-rank premise.

Source: Aschbacher–Smith4.4.9–11, p.621, using A.3.8(1–2), pp.45–46.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Neither odd ternary central-quotient model occurs in the original escaping
nonnormal component. -/
theorem source_a5_oddNormalizer_nonnormal_component_not_odd_three
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) :
    ∀ r : ℕ, r.Prime → Odd r →
      ¬ (ClassicalGroup.IsPSL (K ⧸ center K) 3 r ∨
         ClassicalGroup.IsPSU (K ⧸ center K) 3 r) := by
  obtain ⟨hz,hr⟩ := source_a5_oddNormalizer_nonnormal_component_rank_budget
    D e hn hp B hne hB hBC hBV hperm K hK hnK houtK hFK
  let a : K ≃* K ⧸ center K := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)
  intro r hprime hodd hm
  rcases hm with hm | hm
  · exact ChapterA.QTComponents.linear_three_odd_false hr r hprime hodd (hm.of_mulEquiv a)
  · exact ChapterA.QTComponents.unitary_three_odd_false hr r hprime hodd (hm.of_mulEquiv a)

end CFSG.Quasithin.Chapter10
