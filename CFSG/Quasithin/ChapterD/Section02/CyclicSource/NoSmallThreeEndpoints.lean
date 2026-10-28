module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclic
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeExtraspecial

/-!
# The complete no-small-three branch of cyclic D.2.17

The local commutator classification divides the original small involutions
into cyclic-three and extraspecial-twenty-seven cases. The two source
branches produce the actual normal odd kernel and generating involution,
on the original fully moved representation. No local generation or
normalizer model is imposed as an additional source premise.
Source: Aschbacher–Smith D.2.26–29, pp.191–192.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The full no-small-three source branch returns the literal endpoint
witness on the original actor and module. -/
theorem Hypotheses.no_small_three_localGeneration (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass}
    (hH : IsSQTK K H) (f : H →* G) (honto : Function.Surjective f)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    Nonempty (LocalGeneration ρ) := by
  classical
  by_cases hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3
  · exact h.all_local_cyclic_three_localGeneration hH f honto hq hfive hNo hcyc
  · push Not at hcyc
    obtain ⟨t,ht,hnot⟩ := hcyc
    rcases h.toCoreHypotheses.local_threeCore_alternatives hq hfive hNo ht with
      ⟨hc,_⟩ | ⟨hex,hc,hd,hcent⟩
    · exact (hnot hc).elim
    · exact h.extraspecial_local_threeCore_localGeneration hH f honto hq hfive hNo
        t ht hex hc hd hcent

end CFSG.Quasithin.ChapterD.CyclicSource
