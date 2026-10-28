module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.FiniteExclusions
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.Suzuki.OddSubgroups
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# Rank-one and Janko-one normalizer components

Binary SL₂ and Suzuki groups have cyclic odd Sylow subgroups, contradicting
the doubled odd ranks in the actual local residual. J₁ is excluded by its
certified order, which is squarefree outside two and three. The shared
Theorem C outer-solvability theorem places the residual in each normal
component under the original covering-uniqueness hypothesis.

Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), printed pp.621--623,745.
CatalogueExclusions applies these results to the literal Hall kernel.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hFK : ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K)
include D hn hBC hodd hBV hFK

/-- Binary SL₂ cannot contain the doubled odd ranks of the local residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_binary_sl2_component {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Matrix.SpecialLinearGroup (Fin 2) F) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound D hn B hBC hodd hBV K hFK e
  intro A Q _ _ _ _ p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_subgroup_le p A).trans (Matrix.SL2.binary_odd_primeRank_le_one ho)

/-- Suzuki odd Sylow cyclicity excludes the actual local residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_suzuki_component {m : ℕ} (hm : 0 < m)
    (e : K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound D hn B hBC hodd hBV K hFK e
  intro A Q _ _ _ _ p hp ho
  let : Fact p.Prime := ⟨hp⟩
  let S : Sylow p (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := Classical.choice inferInstance
  have hcyc := BenderSuzuki.MatrixGroups.suzukiSylow_isCyclic_of_ne_two hm
    (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2)) S
  exact (primeRank_subgroup_le p A).trans (S.primeRank_le_one_of_isCyclic hcyc)

/-- The certified J₁ order excludes the paired residual quotient. -/
theorem source_nonnormal_oddNormalizer_no_placed_jankoOne_component (e : K ⧸ center K ≃* Janko1.Model) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_order D hn B hBC hodd hBV K hFK
    (q := 3) (a := 3) (b := 1) (c := 5*7*11*19) Nat.prime_three
  · have h35 : Squarefree (5*7 : ℕ) := (Nat.squarefree_mul (by decide)).mpr
      ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
        (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩
    have h385 : Squarefree (5*7*11 : ℕ) := (Nat.squarefree_mul (by decide)).mpr
      ⟨h35,(Nat.prime_iff.mp (by decide : Nat.Prime 11)).squarefree⟩
    exact (Nat.squarefree_mul (by decide)).mpr
      ⟨h385,(Nat.prime_iff.mp (by decide : Nat.Prime 19)).squarefree⟩
  · rw [Nat.card_congr e.toEquiv,Janko1.card_model]
    decide

omit hFK

/-- The binary SL₂ normal-component exclusion with placement discharged. -/
theorem source_nonnormal_oddNormalizer_no_binary_sl2_component
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {n : ℕ} (hn2 : 2 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2^n)) : False := by
  have hFK := source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
    (.bender (.linear n hn2 hm))
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact source_nonnormal_oddNormalizer_no_placed_binary_sl2_component D hn B hBC hodd hBV K hFK
    (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)

/-- The Suzuki normal-component exclusion with placement discharged. -/
theorem source_nonnormal_oddNormalizer_no_suzuki_component
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {m : ℕ} (hm : 1 ≤ m)
    (e : K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_suzuki_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.bender (.suzuki m hm ⟨e⟩))) (by omega) e

/-- The J₁ normal-component exclusion with placement discharged. -/
theorem source_nonnormal_oddNormalizer_no_jankoOne_component
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (e : K ⧸ center K ≃* Janko1.Model) : False := by
  exact source_nonnormal_oddNormalizer_no_placed_jankoOne_component D hn B hBC hodd hBV K
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inr ⟨e⟩))) e
end CFSG.Quasithin.Chapter10
