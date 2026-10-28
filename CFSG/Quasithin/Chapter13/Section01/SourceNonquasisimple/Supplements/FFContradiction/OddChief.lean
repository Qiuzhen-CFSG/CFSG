module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.OddRank
public import Theory.Representation.NormalElementaryQuotient.RelativeChief
public import Theory.GroupTheory.PResidual.NormalizedImageLift

/-!
# The common chief section for the selected odd-prime line

Lift the actual order-d subgroup K̂_B inside the original K, then take its
two-residual. The lift remains inside K and still maps onto exactly K̂_B.
The canonical factor commutes with K̂_B; the chosen actor normalizes it.
Thus both lifted factors are normal relative to the smaller actor group.

Their nonzero double moved subgroup gives a common chief section in the
literal hat representation. The canonical PSL₂(p) image acts faithfully,
and K̂_B acts nontrivially. Actor generation and the proved rank bound give
ε ≤ 1. The final candidate application now supplies common chief sections
in every refined branch, using the earlier component/cubic construction.

OddExclusion identifies this section with the product input to the proved
repeated-coordinate exclusion. The controlled-index Thompson factorization,
tensor identification and final generation remain with
qt-d-1319-ff-contradiction. Earlier source geometry
remains with qt-d-1317-supplements and qt-d-1317-source.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Stellmacher Theory.GroupTheory
open Representation Representation.BinaryOffender
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02.Adequate Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

structure OddHatChief (T L Y A : Subgroup G) (j d : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    (b : OddHatPrimeLine T L Y A j d) where
  lift : Subgroup (commonGroup T L Y j)
  contained : lift ≤ (thompsonCommutator T L Y j).subgroupOf (commonGroup T L Y j)
  perfect : IsPPerfect 2 lift
  image : lift.map (hatMap T L Y j) = b.subgroup
  chief : CommonChief.Data (hatRepresentation T L Y j)
    (hatImage T L Y j (canonicalSupplement T L)) b.subgroup (hatImage T L Y j A)
    (NormalElementaryQuotient.subspace (commonModule T L Y j)
      ((⁅⁅commonModule T L Y j,(canonicalSupplement T L).subgroupOf (commonGroup T L Y j)⁆,
        lift⁆).subgroupOf (commonModule T L Y j)))

private theorem odd_line_perfect {T L Y A : Subgroup G} {j d : ℕ}
    [(commonModule T L Y j).Normal] (b : OddHatPrimeLine T L Y A j d)
    (hd : d.Prime) (hd2 : d ≠ 2) : IsPPerfect 2 b.subgroup := by
  apply (pResidual_eq_top_iff 2 b.subgroup).mp
  apply top_unique
  intro x _
  apply mem_pResidual_of_orderOf_coprime
  have hc : Nat.Coprime 2 (Nat.card b.subgroup) := by
    rw [b.card]
    exact Nat.coprime_two_left.mpr (hd.odd_of_ne_two hd2)
  exact hc.coprime_dvd_right (orderOf_dvd_natCard x)

/-- The selected prime line has a two-perfect lift inside the original K and
an actual common chief section with the canonical factor. -/
theorem odd_hat_chief (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L H C Y A : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (w : RefinedWitness T L H C Y)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement (T : Subgroup G) L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) {j d : ℕ}
    [(commonModule (T : Subgroup G) L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule (T : Subgroup G) L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (b : OddHatPrimeLine (T : Subgroup G) L Y A j d) (hd : d.Prime) (hd2 : d ≠ 2) :
    Nonempty (OddHatChief (T : Subgroup G) L Y A j d b) := by
  let F := commonGroup (T : Subgroup G) L Y j
  let D := commonModule (T : Subgroup G) L Y j
  let S := (canonicalSupplement (T : Subgroup G) L).subgroupOf F
  let K := (thompsonCommutator (T : Subgroup G) L Y j).subgroupOf F
  let q := hatMap (T : Subgroup G) L Y j
  let Shat := hatImage (T : Subgroup G) L Y j (canonicalSupplement (T : Subgroup G) L)
  let Khat := hatImage (T : Subgroup G) L Y j (thompsonCommutator (T : Subgroup G) L Y j)
  let Ahat := hatImage (T : Subgroup G) L Y j A
  let E := CommonChief.actorGroup Shat b.subgroup Ahat
  have hi := thompson_commutator_invariance w hTH hAH hTL j
  have hKN : F ≤ normalizer (thompsonCommutator (T : Subgroup G) L Y j : Set G) :=
    sup_le (le_sup_left.trans hi.2.2.1)
      (sup_le (thompsonCommutator (T : Subgroup G) L Y j).le_normalizer
        ((radicalSylowCentralizer_le _ _).trans (le_sup_right.trans hi.2.2.1)))
  let : K.Normal := normal_subgroupOf_of_le_normalizer hKN
  let : Khat.Normal := hat_commutator_normal w hTH hAH hTL j
  have hSN : F ≤ normalizer (canonicalSupplement (T : Subgroup G) L : Set G) :=
    sup_le (canonicalSupplement (T : Subgroup G) L).le_normalizer
      (sup_le (hi.1.trans w.normalizes)
        ((radicalSylowCentralizer_le _ _).trans (sylow_normalizes_canonicalSupplement hTL)))
  let : S.Normal := normal_subgroupOf_of_le_normalizer hSN
  have hPK : b.subgroup ≤ Khat := b.contained.trans (commutator_le_left Khat Ahat)
  have hKsecond : Khat ≤ hatImage (T : Subgroup G) L Y j
      (thompsonCommutator (T : Subgroup G) L Y j ⊔ radicalSylowCentralizer (T : Subgroup G) L) :=
    map_mono (subgroupOf_mono F le_sup_left)
  have hcP : ⁅Shat,b.subgroup⁆ = ⊥ := bot_unique
    ((commutator_mono le_rfl (hPK.trans hKsecond)).trans ha.commute.le)
  have hEP : E ≤ normalizer (b.subgroup : Set (HatGroup (T : Subgroup G) L Y j)) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.mp hcP).trans
      (Subgroup.centralizer_le_normalizer _)) (sup_le b.subgroup.le_normalizer b.normalized)
  obtain ⟨B,hBK,hBp,hBq,hBN⟩ := exists_pPerfect_lift_within_normal q K b.subgroup E
    hPK hEP (odd_line_perfect b hd hd2)
  have hcan := canonical_frattini_geometry h hmany hL hn
  have hSp : IsPPerfect 2 S := (mem_L_isPPerfect hcan.1.1).of_surjective
    (subgroupOfEquivOfLe (show canonicalSupplement (T : Subgroup G) L ≤ F from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show canonicalSupplement (T : Subgroup G) L ≤ F from le_sup_left)).symm.surjective
  have hc : ⁅S,B⁆ ≤ centralizer (D : Set F) := by
    rw [←hatMap_ker]
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator,hBq]
    exact hcP
  have hDE : omegaClosure (T : Subgroup G) L Y j ≤ F := (omegaClosure_geometry w hTH hAH hTL j).2.1.trans le_sup_right
  have hmapU : (⁅D,S⁆).map F.subtype =
      ⁅omegaClosure (T : Subgroup G) L Y j,canonicalSupplement (T : Subgroup G) L⁆ := by
    rw [map_commutator]
    change ⁅((omegaClosure (T : Subgroup G) L Y j).subgroupOf F).map F.subtype,
      ((canonicalSupplement (T : Subgroup G) L).subgroupOf F).map F.subtype⁆ = _
    rw [map_subgroupOf_eq_of_le hDE,map_subgroupOf_eq_of_le (show canonicalSupplement (T : Subgroup G) L ≤ F from le_sup_left)]
  have hm : ⁅⁅D,S⁆,B⁆ ≠ ⊥ := by
    intro hz
    have hBC : B ≤ centralizer ((⁅D,S⁆ : Subgroup F) : Set F) :=
      commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact hz)
    have hBU : B ≤ (centralizer
        ((⁅omegaClosure (T : Subgroup G) L Y j,canonicalSupplement (T : Subgroup G) L⁆ : Subgroup G) : Set G)).subgroupOf F := by
      intro x hx u hu
      rw [←hmapU] at hu
      obtain ⟨v,hv,rfl⟩ := hu
      exact congrArg Subtype.val (hBC hx v hv)
    apply b.moves
    rw [←hBq]
    exact map_mono hBU
  have hBnorm : (CommonChief.actorGroup (S.map q) (B.map q) Ahat).comap q ≤
      normalizer (B : Set F) := by
    rw [hBq]
    exact hBN
  obtain ⟨c⟩ := CommonChief.exists_of_relative_double_movement D q
    (QuotientGroup.mk'_surjective _) (hatMap_ker (T : Subgroup G) L Y j)
    S B Ahat le_normalizer_of_normal hBnorm hSp hBp hc hm
  rw [hBq] at c
  exact ⟨⟨B,hBK,hBp,hBq,c⟩⟩

/-- The canonical simple image acts faithfully on the constructed odd chief section. -/
theorem OddHatChief.canonical_faithful {T L Y A : Subgroup G} {j d : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    {b : OddHatPrimeLine T L Y A j d} (c : OddHatChief T L Y A j d b)
    (ha : CommonActionProperties T L Y j) :
    Function.Injective ((sectionRepresentation
      ((hatRepresentation T L Y j).comp
        (CommonChief.actorGroup (hatImage T L Y j (canonicalSupplement T L))
          b.subgroup (hatImage T L Y j A)).subtype)
      c.chief.lower c.chief.upper).comp
        (inclusion (show hatImage T L Y j (canonicalSupplement T L) ≤
          CommonChief.actorGroup (hatImage T L Y j (canonicalSupplement T L))
            b.subgroup (hatImage T L Y j A) from le_sup_left))) := by
  obtain ⟨p,_,hp,F,hF,hfin,hcard,⟨e⟩⟩ := ha.canonical_model
  let := hF
  let := hfin
  let : IsSimpleGroup (GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (hcard ▸ hp)
  let := e.isSimpleGroup
  exact c.chief.first_faithful

/-- Every refined branch of the original outside candidate now supplies its
common chief section. The odd section has a literal two-perfect lift and ε ≤ 1. -/
theorem candidate_common_chief_all_branches (h : Hypothesis1311 T)
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
          ∃ A ∈ thompsonFamily (radicalSylowCentralizer (T : Subgroup G) L) j,
            hatImage (T : Subgroup G) L Y j A ≠ ⊥ ∧ HatActorBound (T : Subgroup G) L Y A j ∧
            ((thompsonCommutator (T : Subgroup G) L Y j = Y ∧
                Nonempty (CommonHatChief (T : Subgroup G) L Y A j)) ∨
              ∃ d : ℕ, d.Prime ∧ 3 < d ∧
                rank (hatImage (T : Subgroup G) L Y j A) ≤ 2 ∧
                ∃ b : OddHatPrimeLine (T : Subgroup G) L Y A j d,
                  ∃ c : OddHatChief (T : Subgroup G) L Y A j d b,
                    c.chief.movedSection.rankLoss ≤ 1) := by
  obtain ⟨Y,w,n,e,ha,_,A,hA,_,hAn,hAb,hcase⟩ :=
    candidate_ranked_moving_actor h hmany hs hrig hclass hL hn hH hTH hne hC hAC hN
  let := n
  let := e
  refine ⟨Y,w,n,e,ha,A,hA,hAn,hAb,?_⟩
  rcases hcase with heq | ⟨_,d,hd,hd3,_,_,_,_,hr,b,hε⟩
  · exact Or.inl heq
  · have hTL := radicalLocal_invariant_source hL.1.1
      (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
    obtain ⟨c⟩ := odd_hat_chief h hmany hL hn w hTH (hAC.trans hC.1) hTL ha b hd (by omega)
    exact Or.inr ⟨d,hd,hd3,hr,b,c,hε c.chief.movedSection⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
