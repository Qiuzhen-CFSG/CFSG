module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddActor
public import Theory.GroupAction.OddSmallRankAutomorphisms
public import Theory.Representation.BinaryOffender.GeneratedActor

/-!
# Rank and section rank loss of the original odd-prime actor

Strong quasithinness bounds the odd-prime rank of Y/O₂(Y). Its exponent and
class bounds imply that every subgroup needs at most two generators. The
literal map from K to its hat-image kills the kernel of K → Y/O₂(Y), so
K̂ also needs at most two generators. Its Frattini automorphism action then
bounds the two-rank of Aut(K̂), and faithfulness bounds the actual Â.

The constructed prime line satisfies K̂_B = [K̂_B,Â]. Any section it moves
is consequently moved by Â, and has rank loss ε ≤ 1. The candidate theorem
retains the same outside maximal two-local, Y, quotient maps and B.2.4 bound.

The odd common chief section is constructed in OddChief, and OddExclusion
uses this rank bound in the literal candidate contradiction. Controlled-index
Thompson factorization, tensor identification and final generation remain
with qt-d-1319-ff-contradiction. The source assembly of
earlier geometry remains with qt-d-1317-supplements and qt-d-1317-source.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871.
-/

public noncomputable section
open scoped IsMulCommutative

open Subgroup Stellmacher Theory.GroupTheory
open Representation Representation.BinaryOffender
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem class_two_of_nilpotencyClass_le_two {P : Type*} [Group P]
    [Group.IsNilpotent P] (hc : Group.nilpotencyClass P ≤ 2) :
    _root_.commutator P ≤ center P := by
  have hz := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hc
  change ⁅_root_.commutator P,(⊤ : Subgroup P)⁆ = ⊥ at hz
  simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz

/-- The literal hat-image of K needs at most two generators in the odd branch. -/
theorem odd_hat_commutator_generator_rank (h : Hypothesis1311 T)
    {L H C Y : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer (T : Subgroup G) L) (j : ℕ)
    [(commonModule (T : Subgroup G) L Y j).Normal]
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hp : IsPGroup d (XiQuotient Y))
    (he : Monoid.exponent (XiQuotient Y) = d)
    (hclass : Group.nilpotencyClass (XiQuotient Y) ≤ 2) :
    Group.rank (hatImage (T : Subgroup G) L Y j
      (thompsonCommutator (T : Subgroup G) L Y j)) ≤ 2 := by
  let : Fact d.Prime := ⟨hd⟩
  let : Group.IsNilpotent (XiQuotient Y) := hp.isNilpotent
  let K := thompsonCommutator (T : Subgroup G) L Y j
  let E := commonGroup (T : Subgroup G) L Y j
  have hKY := (thompson_commutator_invariance w hTH hAH hTL j).1
  have hKE : K ≤ E := le_sup_left.trans le_sup_right
  let f : K →* XiQuotient Y := (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hKY)
  let g : K →* hatImage (T : Subgroup G) L Y j K :=
    ((hatMap (T : Subgroup G) L Y j).subgroupMap (K.subgroupOf E)).comp
      (subgroupOfEquivOfLe hKE).symm.toMonoidHom
  have hg : Function.Surjective g :=
    ((hatMap (T : Subgroup G) L Y j).subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe hKE).symm.surjective
  have hk : f.ker ≤ g.ker := by
    intro x hx
    have hy : (⟨x.val,hKY x.property⟩ : Y) ∈ pCore 2 Y :=
      (QuotientGroup.eq_one_iff _).mp hx
    apply Subtype.ext
    change hatMap (T : Subgroup G) L Y j ⟨x.val,hKE x.property⟩ = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    intro u hu
    exact Subtype.ext (escaping_core_centralizes_omegaClosure h w hH hTH hAH hTL hcore j
      (mem_map_of_mem Y.subtype hy) u hu)
  have hrY : primeRank d (XiQuotient Y) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup d (hd.odd_of_ne_two hd2) _ pCore_isPGroup).trans
      ((_root_.primeRank_mono d w.witness.le_overgroup).trans
        ((h.simpleQTKE.twoLocal_sqtk hH.1).stronglyQuasithin d hd (hd.odd_of_ne_two hd2)))
  exact (Group.rank_le_range_of_ker_le f g hg hk).trans
    (hp.subgroup_rank_le_two_of_exponent_prime_class_two hd2
      (fun x => he ▸ Monoid.pow_exponent_eq_one x)
      (class_two_of_nilpotencyClass_le_two hclass) hrY f.range)

/-- The faithful elementary Thompson actor has rank at most two. -/
theorem odd_hat_actor_rank (h : Hypothesis1311 T)
    {L H C Y A : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer (T : Subgroup G) L) {j : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hp : IsPGroup d (XiQuotient Y))
    (he : Monoid.exponent (XiQuotient Y) = d)
    (hclass : Group.nilpotencyClass (XiQuotient Y) ≤ 2) :
    rank (hatImage (T : Subgroup G) L Y j A) ≤ 2 := by
  let : Fact d.Prime := ⟨hd⟩
  let K := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
  let B := hatImage (T : Subgroup G) L Y j A
  let := hat_commutator_normal w hTH hAH hTL j
  have hBN : B ≤ normalizer (K : Set (HatGroup (T : Subgroup G) L Y j)) :=
    le_normalizer_of_normal
  let a : B →* MulAut K := K.normalizerMonoidHom.comp (inclusion hBN)
  have hi : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply bot_unique
    intro b hb
    apply Subtype.ext
    have hbC : (b : HatGroup (T : Subgroup G) L Y j) ∈ centralizer (K : Set _) := by
      change inclusion hBN b ∈ K.normalizerMonoidHom.ker at hb
      rwa [normalizerMonoidHom_ker] at hb
    exact mem_bot.mp (common_actor_faithful ha hA ▸ ⟨b.property,hbC⟩)
  have hrK := odd_hat_commutator_generator_rank h w hH hTH hAH hTL hcore j hd hd2 hp he hclass
  have hrB : primeRank 2 B ≤ 2 :=
    (_root_.primeRank_le_of_injective 2 a hi).trans
      ((odd_hat_commutator_isPGroup h w hH hTH hAH hTL hcore j hp).automorphism_twoRank_le_two_of_rank_le_two hd2 hrK)
  let : IsElementaryAbelian 2 A := hA.2.1
  have hAE : A ≤ commonGroup (T : Subgroup G) L Y j :=
    hA.1.trans (le_sup_right.trans le_sup_right)
  let : IsElementaryAbelian 2 (A.subgroupOf (commonGroup (T : Subgroup G) L Y j)) :=
    IsElementaryAbelian.subgroupOf hAE
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (hatMap (T : Subgroup G) L Y j)
  change Nat.log 2 (Nat.card B) ≤ 2
  rw [IsElementaryAbelian.log_card_eq_primeRank (p := 2)]
  exact hrB

/-- On a section moved by the actual prime line, the source's rank loss is at most one. -/
theorem OddHatPrimeLine.section_rankLoss_le_one
    {T L Y A : Subgroup G} {j d : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    (b : OddHatPrimeLine T L Y A j d)
    (hA : IsElementaryTwo (hatImage T L Y j A))
    (hr : rank (hatImage T L Y j A) ≤ 2)
    (s : RepeatedSectionBudget.MovedSection (hatRepresentation T L Y j)
      b.subgroup (hatImage T L Y j A)) : s.rankLoss ≤ 1 :=
  s.rankLoss_le_one_of_generated b.generated hA hr

/-- The original outside candidate supplies the moving actor and, in the
larger odd-prime branch, its rank bound and rank-loss bound on every moved section.
OddChief constructs that branch's common chief section. -/
theorem candidate_ranked_moving_actor (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement (T : Subgroup G) L ≤ C)
    {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ∃ n : (commonModule (T : Subgroup G) L Y j).Normal,
        let := n
        ∃ e : IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j),
          let := e
          CommonActionProperties (T : Subgroup G) L Y j ∧
          hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j) =
            ⁅hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j),
              hatImage (T : Subgroup G) L Y j (thompsonJ (radicalSylowCentralizer (T : Subgroup G) L) j)⁆ ∧
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            ⁅⁅omegaClosure (T : Subgroup G) L Y j,canonicalSupplement (T : Subgroup G) L⁆,
              ⁅thompsonCommutator (T : Subgroup G) L Y j,A⁆⁆ ≠ ⊥ ∧
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧ HatActorBound (T : Subgroup G) L Y A j ∧
            ((thompsonCommutator (T : Subgroup G) L Y j = Y ∧
                Nonempty (CommonHatChief (T : Subgroup G) L Y A j)) ∨
              (IsPPerfect 2 Y ∧ ∃ d : ℕ, d.Prime ∧ 3 < d ∧
                IsPGroup d (XiQuotient Y) ∧ Monoid.exponent (XiQuotient Y) = d ∧
                Group.nilpotencyClass (XiQuotient Y) ≤ 2 ∧
                IsPGroup d (hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)) ∧
                rank (hatImage (T : Subgroup G) L Y j A) ≤ 2 ∧
                ∃ b : OddHatPrimeLine (T : Subgroup G) L Y A j d,
                  ∀ s : RepeatedSectionBudget.MovedSection (hatRepresentation (T : Subgroup G) L Y j)
                    b.subgroup (hatImage (T : Subgroup G) L Y j A), s.rankLoss ≤ 1)) := by
  obtain ⟨Y,w,n,e,ha,hid,A,hA,hm,hAn,hAb,hcase⟩ :=
    candidate_common_moving_actor h hmany hs hrig hclass hL hn hH hTH hne hC hAC hN
  let := n
  let := e
  refine ⟨Y,w,n,e,ha,hid,A,hA,hm,hAn,hAb,?_⟩
  rcases hcase with heq | ⟨hpY,d,hd,hd3,hp,he,hc,hpk,⟨b⟩⟩
  · exact Or.inl heq
  · have hTL := radicalLocal_invariant_source hL.1.1
      (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
    have hcore := (canonical_frattini_geometry h hmany hL hn).2.1
    have hr := odd_hat_actor_rank h w hH hTH (hAC.trans hC.1) hTL hcore ha hA
      hd (by omega) hp he hc
    exact Or.inr ⟨hpY,d,hd,hd3,hp,he,hc,hpk,hr,b,
      fun s => b.section_rankLoss_le_one hAb.1 hr s⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
