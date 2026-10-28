module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.LinearThreeExclusion.EvenModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.StarTransport
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2Even.TwoRank.Elementary
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Excluding odd PSL₃ from the actual C.2.7 star catalogue

Pass every literal model identification to its central quotient. The even
linear groups are excluded by the existing rank and order comparisons.
Even Sp₄ and G₂ have two-rank at least three, whereas odd PSL₃ has two-rank
at most two. The fixed exceptional and alternating rows are excluded by
their actual orders, including the center quotient of the triple cover.

For the original C.2.7 input, the proved kernel bound gives the central-cover
comparison between K/O₂(K) and K*. Their central quotients are isomorphic,
so the catalogue excludes both SL₃(p) and PSL₃(p) without block hypotheses.
Source: Aschbacher–Smith, proof of 1.3.8, p.514; C.2.7, pp.145–147.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.LinearThreeExclusion

private def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr (center A) (center B) e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

private theorem odd_projective_rank_le_two {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hm : ClassicalGroup.IsPSL Q 3 p) :
    primeRank 2 Q ≤ 2 := by
  let S : Sylow 2 Q := Classical.arbitrary _
  rw [S.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le S).mpr
  intro E hE
  exact (ABG.rank_two_and_cyclic_center_of_sylow_shape
    (XiEmbedding.InvariantLarge.OddCartan.isPSL_sylow_shape ho hm S)).2.1 E hE

/-- Every genuine star model has central quotient different from odd PSL₃(p), p ≥ 5. -/
theorem starModel_not_odd_linearThree {A : Type*} [Group A] [Finite A]
    (h : ChapterC.C27Source.StarModels.Model A) {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (ho : Odd p) : ¬ ClassicalGroup.IsPSL (A ⧸ center A) 3 p := by
  intro hm
  cases h with
  | linearTwo F e =>
    have he : ClassicalGroup.IsPSL (A ⧸ center A) 2 (2 ^ F.degree) :=
      ⟨F.Carrier, inferInstance, inferInstance, F.card_eq, ⟨centerQuotientCongr e⟩⟩
    exact not_even_rankOne_model hp ho (Or.inr hm) he
  | linearThree F e =>
    have he : ClassicalGroup.IsPSL (A ⧸ center A) 3 (2 ^ F.degree) :=
      ⟨F.Carrier, inferInstance, inferInstance, F.card_eq, ⟨centerQuotientCongr e⟩⟩
    exact not_even_projective_model hp ho hm he
  | symplectic F large e =>
    have hr := odd_projective_rank_le_two ho hm
    rw [primeRank_equiv 2 (centerQuotientCongr e),
      Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_rank F.card_eq F.degree_pos] at hr
    omega
  | g2 F large e =>
    have hcard : 2 < Nat.card F.Carrier := by
      rw [F.card_eq]
      exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) large
    let _ := Atlas.G2.isSimple hcard
    let _ := Atlas.G2.isPerfect hcard
    have hz : center (Atlas.G2.Model F.Carrier) = ⊥ := by
      rcases (inferInstance : (center (Atlas.G2.Model F.Carrier)).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative (Atlas.G2.Model F.Carrier)
          (center_eq_top_iff.mp hz)).elim
    let ec : (A ⧸ center A) ≃* Atlas.G2.Model F.Carrier :=
      (centerQuotientCongr e).trans
        ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)
    have hr := odd_projective_rank_le_two ho hm
    rw [primeRank_equiv 2 ec] at hr
    have hl := Atlas.G2.EvenTwoRank.rank_ge F.Carrier F.card_eq
    omega
  | g2DerivedTwo e =>
    have hc : Nat.card A = 6048 := by
      rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    have hle := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center A))
    exact not_linearThree_of_small_order hp (by omega) (Or.inr hm)
  | alternating n degree e =>
    have hc : Nat.card A ≤ 20160 := by
      rcases degree with rfl | rfl | rfl | rfl <;>
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] <;> norm_num
    have hle := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center A))
    exact not_linearThree_of_small_order hp (by omega) (Or.inr hm)
  | linearFiveTwo e =>
    have he : ClassicalGroup.IsPSL (A ⧸ center A) 5 2 :=
      ⟨ZMod 2, inferInstance, inferInstance, by simp, ⟨centerQuotientCongr e⟩⟩
    obtain ⟨F, _, _, hF, ⟨ec⟩⟩ := he
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [← Nat.card_congr ec.toEquiv, hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact not_linearThree_of_large_exceptional_order hp (Or.inr hc) (Or.inr hm)
  | tripleSix _ e =>
    have hc : Nat.card (A ⧸ center A) ≤ 20160 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    exact not_linearThree_of_small_order hp hc (Or.inr hm)

/-- The exact original C.2.7 input excludes the odd linear-three quotient.
The comparison uses the actual central cover from K/O₂(K) to K*. -/
theorem not_linearThree_of_source {G : Type*} [Group G] [Finite G]
    {H R M K : Subgroup G}
    (h : FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple H R M K)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (ho : Odd p) :
    ¬ XiEmbedding.LinearThreeModel p (XiQuotient K) := by
  intro hm
  have hb : StarKernelBound K R := (ChapterC.C27Source.kernel_offender_from_source h).1.upper
  have hstar := (linearThree_center_model hm).of_mulEquiv
    (coreStarCenterEquiv h.normalizes h.quasisimple
      (starImage_ne_bot_of_bound h.normalizes h.quasisimple hb)).symm
  exact starModel_not_odd_linearThree (ChapterC.C27Source.star_model_from_source h) hp ho hstar

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction
