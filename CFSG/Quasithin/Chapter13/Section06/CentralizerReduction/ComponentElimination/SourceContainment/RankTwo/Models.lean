module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.Basic
public import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.HexacodeAction.ThreeRank
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.PrimeRankZero

/-!
# The actual reduced model list and the source three-rank split

The seven models left after 13.6.18–19 are represented by genuine
multiplicative equivalences. The symplectic and G₂ entries use their
commutator subgroups, and the triple cover of A₆ is the concrete hexacode
carrier. Every entry except PSL₃(2) contains an elementary abelian nine.

If the original component has three-rank at most one, its Sylow
three-subgroups are cyclic, so the same is true of its actual plus image.
This excludes the other six entries. The surviving image has order 168,
which also excludes rank zero in the original component. The application
uses the literal surjection K → K* → K+, with no asserted equality of
ranks across an arbitrary quotient.

The list itself and the ambient three-rank bound remain earlier source
inputs. This module proves the split, not the rank-two theta identity.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
13.6.20, printed p.931. Concrete ATLAS attributions are retained in the
imported model modules.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
open ComponentSelection

/-- The seven concrete possibilities following 13.6.18–19. -/
inductive ReducedModel (Q : Type*) [Group Q] : Prop
  | linear (n : ℕ) (hn : 3 ≤ n ∧ n ≤ 5) (iso : Nonempty (Q ≃* PSL(n, ZMod 2)))
  | symplectic (iso : Nonempty (Q ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
  | g2 (iso : Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | ahat6 (iso : Nonempty (Q ≃* Atlas.Codes.HexEvenAutomorphisms))
  | a7 (iso : Nonempty (Q ≃* alternatingGroup (Fin 7)))

/-- Every reduced model other than the actual PSL₃(2) has three-rank at least two. -/
theorem reduced_model_rank_alternative {Q : Type*} [Group Q] [Finite Q]
    (h : ReducedModel Q) :
    Nonempty (Q ≃* Matrix.PSL3Two.PSL) ∨ 2 ≤ primeRank 3 Q := by
  cases h with
  | linear n hn he =>
      obtain ⟨e⟩ := he
      by_cases hn3 : n = 3
      · subst n
        exact Or.inl ⟨e⟩
      · right
        rw [primeRank_equiv 3 (e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)))]
        exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank (by omega)
  | symplectic he =>
      obtain ⟨e⟩ := he
      right
      rw [primeRank_equiv 3 e]
      exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic
  | g2 he =>
      obtain ⟨e⟩ := he
      right
      rw [primeRank_equiv 3 e]
      exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  | ahat6 he =>
      obtain ⟨e⟩ := he
      right
      rw [primeRank_equiv 3 e]
      exact Representation.Hexacode.two_le_primeRank_even
  | a7 he =>
      obtain ⟨e⟩ := he
      right
      rw [primeRank_equiv 3 e]
      exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

/-- Rank one passes to a surjective image through cyclic Sylow three-subgroups. -/
theorem rank_split_of_surjective {K Q : Type*} [Group K] [Finite K]
    [Group Q] [Finite Q] (f : K →* Q) (hf : Function.Surjective f)
    (hr : primeRank 3 K ≤ 2) (hmodel : ReducedModel Q) :
    primeRank 3 K = 2 ∨
      primeRank 3 K = 1 ∧ Nonempty (Q ≃* Matrix.PSL3Two.PSL) := by
  by_cases htwo : primeRank 3 K = 2
  · exact Or.inl htwo
  have hr1 : primeRank 3 K ≤ 1 := by omega
  let P : Sylow 3 K := Classical.choice inferInstance
  have hq1 := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr1) f hf
  rcases reduced_model_rank_alternative hmodel with he | hq2
  · obtain ⟨e⟩ := he
    right
    refine ⟨?_, ⟨e⟩⟩
    have hnz : primeRank 3 K ≠ 0 := by
      intro hz
      have hq0 := PrimeRank.eq_zero_of_surjective f hf hz
      have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hq0
      rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_PSL] at hn
      exact hn (by decide)
    omega
  · omega

variable {G : Type*} [Group G] [Finite G]

/-- The source split on actual Y_z and K+ carriers. The bound on C_G(v)
is supplied by the earlier SQTK conclusion. -/
theorem source_rank_split (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (hr : primeRank 3 (Gv v) ≤ 2)
    (hmodel : ReducedModel (plusImage K L T z v hL hz K)) :
    primeRank 3 K = 2 ∨ primeRank 3 K = 1 ∧
      Nonempty (plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL) := by
  let f := (componentStarToPlus K L T z v hK.1.1 hL hz).comp
    (starImageMap z v K hK.1.1)
  exact rank_split_of_surjective f
    ((componentStarToPlus_surjective K L T z v hK.1.1 hL hz).comp
      (starImageMap_surjective z v K hK.1.1))
    ((primeRank_le_of_injective 3 (inclusion hK.1.1) (inclusion_injective hK.1.1)).trans hr)
    hmodel
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
