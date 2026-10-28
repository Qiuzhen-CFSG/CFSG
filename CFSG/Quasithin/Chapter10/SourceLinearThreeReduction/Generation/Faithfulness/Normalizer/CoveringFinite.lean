module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringAction

/-!
# Finite constrained rows for a simple seed

The alternating, triple-six, binary degree-five and derived G₂ star rows
have cubic rank at least two and rank at most one at the other odd primes.
The actual C.2.7 central-cover maps and certified model orders discharge
these bounds. The simple-seed action argument then gives local normality.

Source: Aschbacher--Smith C.2.7 and C.4.5--8, pp.145--154, used in
4.4.6, p.620. CoveringConstrained assembles these model exclusions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The finite alternating rows have cubic rank two and no other odd
rank above one. This uses the actual central quotient. -/
theorem normalizes_of_simple_constrained_central_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : 6 ≤ n) (hn9 : n ≤ 9)
    (e : coreCentralQuotient K ≃* alternatingGroup (Fin n)) :
    M ≤ normalizer (L : Set G) := by
  apply h.normalizes_of_simple_constrained_central_ranks hz K hK hq hout hfK
  · rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank hn
  · intro p hp ho hp3
    rw [primeRank_congr p e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime n p hp
        (by intro he; subst p; exact ho.not_two_dvd_nat (dvd_refl 2))]
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      have := ho.not_two_dvd_nat
      omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))

/-- Transport the alternating star marking through the original C.2.7
central-cover map. -/
theorem normalizes_of_simple_constrained_star_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : 6 ≤ n) (hn9 : n ≤ 9)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin n)) :
    M ≤ normalizer (L : Set G) := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))))
  exact h.normalizes_of_simple_constrained_central_alternating hz K hK hq hout hfK hn hn9 ec

/-- The triple-six row retains its literal star central quotient. -/
theorem normalizes_of_simple_constrained_star_triple_six
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : (starImage (K.map H.subtype) R (K.map H.subtype) ⧸
      center (starImage (K.map H.subtype) R (K.map H.subtype))) ≃*
      alternatingGroup (Fin 6)) : M ≤ normalizer (L : Set G) := by
  exact h.normalizes_of_simple_constrained_central_alternating hz K hK hq hout hfK
    (by decide) (by decide) ((h.constrained_star_central_equiv K hK hq hout hfK).trans e)

private theorem binary_five_card {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) = 9999360 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hF,Fin.prod_univ_succ] at hc
  exact hc

/-- The binary degree-five star row is eliminated from its actual projective order. -/
theorem normalizes_of_simple_constrained_star_linear_five_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : M ≤ normalizer (L : Set G) := by
  let ec := (h.constrained_star_central_equiv K hK hq hout hfK).trans
    (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e))
  have hc : Squarefree (1085 : ℕ) :=
    (Nat.squarefree_mul (show Nat.Coprime 35 31 by decide)).mpr
      ⟨(Nat.squarefree_mul (show Nat.Coprime 5 7 by decide)).mpr
        ⟨(Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree,
          (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree⟩,
        (Nat.prime_iff.mp (by decide : Nat.Prime 31)).squarefree⟩
  refine h.normalizes_of_simple_constrained_central_order hz K hK hq hout hfK
    (a := 10) (b := 2) (c := 1085) ?_ hc ?_
  · rw [primeRank_congr 3 ec]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  · rw [Nat.card_congr ec.toEquiv,binary_five_card (by simp : Nat.card (ZMod 2) = 2)]
    decide

/-- The derived binary G₂ star row is eliminated from its certified order. -/
theorem normalizes_of_simple_constrained_star_g2_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hz : center (L ⧸ pCore 2 L) = ⊥)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : M ≤ normalizer (L : Set G) := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)
  refine h.normalizes_of_simple_constrained_central_order hz K hK hq hout hfK
    (a := 5) (b := 3) (c := 7) ?_
    (Nat.prime_iff.mp (by decide : Nat.Prime 7)).squarefree ?_
  · rw [primeRank_congr 3 ec]
    exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2
  · rw [Nat.card_congr ec.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide
end CFSG.Quasithin.ChapterC.HypothesisC28
