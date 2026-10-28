module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.PairSylow
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryLocal
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.UnitaryFrattiniBoundary
public import Theory.SpecificGroups.FiniteModelTwoRank
public import Theory.SpecificGroups.Janko3.Model.FrattiniSixteen
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.FrattiniSixteen
public import Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen

/-!
# Four remaining component exclusions from actual Sylow bounds

The original residual acts innerly on each normal component whose central
quotient has a Sylow with at most five Frattini generators. Covering
uniqueness then places the full residual in that component. The actual
J₃ and McL rank and order bounds, the binary symplectic-six order, and the
binary unitary-four two-local bound give contradictions. No outer-solvability
callback or restriction on the original component marking remains.

These are applications to the literal odd Hall-kernel actor, preserving the
whole moved module and the full covering centers. Source: Aschbacher--Smith
4.4.10--12 and 10.2.3(2), printed pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
  (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hp hB hBC hBV hperm hK hout

/-- The actual five-generator Sylow bound supplies residual placement,
with covering uniqueness discharged on the original odd actor. -/
theorem source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card (P ⧸ frattini P) ≤ 32) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K := by
  let : IsQuasisimple K := hK.2
  have ho : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp B hB hBC hBV hperm
  exact (source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    D hn B hBC ho hBV hu K hK hout (le_trans le_top le_normalizer_of_normal)
    (source_nonnormal_oddNormalizer_inner_of_smallFrattini
      D hn hp B hB hBC hperm K P hP)).2.2.2

omit D hn hBC hBV hperm hK hout in
private theorem odd_card : Odd (Nat.card B) := by
  obtain ⟨n,he⟩ := hB.exists_card_eq
  rw [he]
  exact hp.pow

/-- J₃ is excluded with its actual center quotient and original module. -/
theorem source_nonnormal_oddNormalizer_no_jankoThree_component
    (hc : pCore 2 K = ⊥) (e : K ⧸ center K ≃* Sporadic.Janko3.Model) : False := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P
    ((Sporadic.Janko3.TwoLocal.sylow_frattini_card_le_sixteen e P).trans (by decide))
  apply source_nonnormal_oddNormalizer_no_placed_small_rank_component
    D hn B hBC (odd_card hp B hB) hBV K hc hFK
  · rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.FiniteModelTwoRank.j3_le_seven
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Sporadic.Janko3.model_card]
    decide

/-- McL is excluded by its certified Sylow, two-rank and seven-part bounds. -/
theorem source_nonnormal_oddNormalizer_no_mcl_component
    (hc : pCore 2 K = ⊥) (e : K ⧸ center K ≃* Sporadic.LeechRelated.McL.Carrier) : False := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P
    ((Sporadic.LeechRelated.McL.FrattiniSixteen.sylow_frattini_card_le_sixteen_of_equiv e P).trans (by decide))
  apply source_nonnormal_oddNormalizer_no_placed_small_rank_component
    D hn B hBC (odd_card hp B hB) hBV K hc hFK
  · rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.FiniteModelTwoRank.mcl_le_seven
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
      Atlas.Sporadic.McLaughlin.card]
    norm_num [Atlas.Sporadic.McLaughlin.order]

/-- The binary symplectic-six row now has its placement premise discharged. -/
theorem source_nonnormal_oddNormalizer_no_binary_symplectic_component
    (hm : ClassicalGroup.IsPSp (K ⧸ center K) 3 2) : False := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P
    ((Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen.frattini_card_le_sixteen_of_equiv
      hF e P).trans (by decide))
  exact source_nonnormal_oddNormalizer_no_placed_binary_symplectic_component
    D hn B hBC (odd_card hp B hB) hBV K hFK ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩

/-- The exact three-generator Sylow quotient closes PSU₄(2). -/
theorem source_nonnormal_oddNormalizer_no_binary_unitary_four_two_component
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 2) : False := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  have hmod : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2^1) := hm
  have hP : Nat.card (P ⧸ frattini P) ≤ 32 := by
    rw [binary_unitary_four_sylow_frattini_card (by decide : 0 < 1) hmod P]
    decide
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P hP
  exact source_nonnormal_oddNormalizer_no_placed_unitary_four_component
    D hn B hBC (odd_card hp B hB) hBV K hFK (by decide : 0 < 1) hmod

end CFSG.Quasithin.Chapter10
