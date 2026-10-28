module
public import Theory.GroupAction.FaithfulElementaryRank
public import Theory.Representation.NormalElementaryQuotient.CommonChief.Displacement
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.SurvivingImage

/-!
# Sharp displacement in the original escaping candidate

The perfect canonical factor forces displacement at least three on the
constructed common chief section. The actual quotient models bound the
faithful actor's rank by two. Together with B.2.4 and j at most one, this
forces j = 1, actor rank two, and displacement exactly three on both the
original module and the section. The cyclic-three branch is impossible.

This proves the numerical equality in (*) of Aschbacher--Smith 13.1.9,
printed p.871, without assuming the tensor model. The original controlled
normalizer input remains explicit: its factorization, tensor recognition,
and the final generation contradiction belong to this task's final assembly.
Earlier canonical geometry is discharged by qt-d-1317-supplements.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin ChapterB Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate Chapter12.Section02 ChapterA.Section04 Escape
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The surviving actual quotient models have automorphism two-rank at most two. -/
theorem small_quotient_automorphism_rank {Q : Type*} [Group Q] [Finite Q]
    (h : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL Q 3 2 ∨ Nonempty (Q ≃* Multiplicative (ZMod 3))) :
    primeRank 2 (MulAut Q) ≤ 2 := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact (primeRank_equiv 2
      Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv).symm.le.trans
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  rcases h with h | h
  · obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h
    let := hF
    let := hfin
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two F hcard).le
  · obtain ⟨e⟩ := h
    have hcard : Nat.card Q = 3 := (Nat.card_congr e.toEquiv).trans (by simp)
    let : IsCyclic Q := isCyclic_of_prime_card hcard
    have hAut : Nat.card (MulAut Q) = 2 := by rw [IsCyclic.card_mulAut,hcard]; decide
    apply (primeRank_le_iff_elementary_card_le (MulAut Q)).mpr
    intro A _
    exact (Nat.card_le_card_of_injective A.subtype A.subtype_injective).trans (by rw [hAut]; decide)

/-- The original canonical supplement remains perfect in the actual action image. -/
theorem common_canonical_perfect (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L Y : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal] :
    Group.IsPerfect (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L)) := by
  let S := canonicalSupplement (T : Subgroup G) L
  let F := commonGroup (T : Subgroup G) L Y j
  let : Group.IsPerfect S := mem_L_isPerfect (canonical_frattini_geometry h hmany hL hn).1.1
  let : Group.IsPerfect (S.subgroupOf F) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show S ≤ F from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show S ≤ F from le_sup_left)).symm.surjective
  exact Group.IsPerfect.map (H := S.subgroupOf F) (hatMap (T : Subgroup G) L Y j)

/-- The common chief section forces at least three dimensions of ambient displacement. -/
theorem common_chief_actor_displacement (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (c : CommonHatChief (T : Subgroup G) L Y A j) :
    3 ≤ fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
      (hatImage (T : Subgroup G) L Y j A) := by
  let := common_canonical_perfect h hmany hL hn (Y := Y) (j := j)
  have he := common_chief_section_epsilon w hTH hAH hTL ha hA c
  have hc : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥ := by
    apply bot_unique
    apply (commutator_mono le_rfl (sup_le
      (map_mono (subgroupOf_mono _ le_sup_left))
      (map_mono (subgroupOf_mono _ (hA.1.trans le_sup_right))))).trans ha.commute.le
  exact (c.actor_displacement hc (ha.actor_bound A hA hAn).1 he).trans c.actor_displacement_le

/-- Faithfulness on the actual K-image bounds the Thompson actor rank by two. -/
theorem common_actor_rank_le_two {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (hmodel : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2 ∨
      Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3)))
    (he : Nonempty (XiQuotient Y ≃*
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))) :
    rank (hatImage (T : Subgroup G) L Y j A) ≤ 2 := by
  let := hat_commutator_normal w hTH hAH hTL j
  obtain ⟨e⟩ := he
  have hr := small_quotient_automorphism_rank hmodel
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  exact (actor_rank_le_automorphism_rank _ _ le_normalizer_of_normal
    (common_actor_faithful ha hA) (ha.actor_bound A hA hAn).1.2).trans hr

/-- A cyclic-three quotient has automorphism rank one and cannot supply the required displacement. -/
theorem common_chief_cyclic_false (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j : ℕ} (hj : j ≤ 1)
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    [IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    (hAn : hatImage (T : Subgroup G) L Y j A ≠ ⊥)
    (c : CommonHatChief (T : Subgroup G) L Y A j)
    (he : Nonempty (XiQuotient Y ≃*
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)))
    (hcyc : Nonempty (XiQuotient Y ≃* Multiplicative (ZMod 3))) : False := by
  let K := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
  obtain ⟨e⟩ := he
  obtain ⟨ec⟩ := hcyc
  have hcard : Nat.card K = 3 := (Nat.card_congr (e.symm.trans ec).toEquiv).trans (by simp)
  let : IsCyclic K := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut K) = 2 := by rw [IsCyclic.card_mulAut,hcard]; decide
  have hrAut : primeRank 2 (MulAut K) ≤ 1 := by
    apply (primeRank_le_iff_elementary_card_le (MulAut K)).mpr
    intro B _
    exact (Nat.card_le_card_of_injective B.subtype B.subtype_injective).trans (by rw [hAut]; decide)
  let := hat_commutator_normal w hTH hAH hTL j
  have hr : rank (hatImage (T : Subgroup G) L Y j A) ≤ 1 :=
    (actor_rank_le_automorphism_rank K _ le_normalizer_of_normal
      (common_actor_faithful ha hA) (ha.actor_bound A hA hAn).1.2).trans hrAut
  have hl := common_chief_actor_displacement h hmany hL hn w hTH hAH hTL ha hA hAn c
  have hb := (ha.actor_bound A hA hAn).2
  omega

/-- The original candidate attains the displacement bound and has a nonabelian
simple quotient. The controlled index remains the source factorization input. -/
theorem candidate_common_chief_sharp (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ} (hj : j ≤ 1)
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    j = 1 ∧ ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          thompsonCommutator (T : Subgroup G) L Y j = Y ∧
          thompsonCommutator (T : Subgroup G) L Y j =
            ⁅thompsonCommutator (T : Subgroup G) L Y j,
              thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j⁆ ∧
          (Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
            ClassicalGroup.IsPSL (XiQuotient Y) 3 2) ∧
          Nonempty (XiQuotient Y ≃*
            hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
          IsSimpleGroup (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧ HatActorBound (T : Subgroup G) L Y A j ∧
            rank (hatImage (T : Subgroup G) L Y j A) = 2 ∧
            fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
              (hatImage (T : Subgroup G) L Y j A) = 3 ∧
            ∃ c : CommonHatChief (T : Subgroup G) L Y A j,
              c.movedSection.rankLoss = 0 ∧
              fixedCodim (sectionRepresentation
                ((hatRepresentation (T : Subgroup G) L Y j).comp
                  (CommonChief.actorGroup
                    (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L))
                    (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))
                    (hatImage (T : Subgroup G) L Y j A)).subtype) c.lower c.upper)
                ((hatImage (T : Subgroup G) L Y j A).subgroupOf
                  (CommonChief.actorGroup
                    (hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L))
                    (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j))
                    (hatImage (T : Subgroup G) L Y j A))) = 3 := by
  obtain ⟨Y,w,n,e,ha,hKY,hgen,hmodel,heq,hsimple,A,hA,hAn,hAb,c,hε⟩ :=
    candidate_common_chief_simple h hmany hs hrig hclass hL hn hH hTH hne hC hAC hj hN
  let := n
  let := e
  let := hsimple
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hAH := hAC.trans hC.1
  have hr := common_actor_rank_le_two w hTH hAH hTL ha hA hAn hmodel heq
  have hl := common_chief_actor_displacement h hmany hL hn w hTH hAH hTL ha hA hAn c
  have hb := hAb.2
  have hj1 : j = 1 := by omega
  have hr2 : rank (hatImage (T : Subgroup G) L Y j A) = 2 := by omega
  have hc3 : fixedCodim (hatRepresentation (T : Subgroup G) L Y j)
      (hatImage (T : Subgroup G) L Y j A) = 3 := by omega
  have hmodel' : Nonempty (XiQuotient Y ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (XiQuotient Y) 3 2 := by
    rcases hmodel with h5 | h3 | hcyc
    · exact Or.inl h5
    · exact Or.inr h3
    · exact (common_chief_cyclic_false h hmany hL hn w hTH hAH hTL hj ha hA hAn c heq hcyc).elim
  refine ⟨hj1,Y,w,n,e,ha,hKY,hgen,hmodel',heq,hsimple,A,hA,hAn,hAb,hr2,hc3,c,hε,?_⟩
  have hupper := c.actor_displacement_le
  -- The section lower bound is retained separately by the generic common-chief theorem.
  let := common_canonical_perfect h hmany hL hn (Y := Y) (j := j)
  have hcomm : ⁅hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L),
      hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) ⊔
        hatImage (T : Subgroup G) L Y j A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono le_rfl (sup_le
      (map_mono (subgroupOf_mono _ le_sup_left))
      (map_mono (subgroupOf_mono _ (hA.1.trans le_sup_right))))).trans ha.commute.le
  have hlower := c.actor_displacement hcomm hAb.1 hε
  omega
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
