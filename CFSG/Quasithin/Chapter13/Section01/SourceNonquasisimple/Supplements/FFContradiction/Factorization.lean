module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.ControlledIndex
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Factorization.LocalObstruction

/-!
# The local Thompson-factorization obstruction on the literal XR

For X = XiP(p,L) and R = radicalSylowCentralizer(T,L), the canonical source
geometry gives the rank, 3-prime order, and characteristic-two hypotheses
needed by the local G.26.18(a) argument. The selected near-maximum B, local
normalizer N, its kernel Sylow subgroup Q, and odd minimal normal section retain their
actual ambient inclusions and quotient map. The local elementary module,
chain control, centralizer bound, and contradiction are supplied by the
proved Thompson factorization obstruction. The source kernel Sylow condition
and odd chief quotient identify Q with O2(N), so that identity is not assumed.

This proves the contradiction after the source's local selection. Constructing
that selection from a failure of ControlledIndexFactorization remains in
qt-d-1319-ff-contradiction, along with its final application to the already
proved candidate_false_of_controlled_factorization in Generation. Earlier
canonical geometry and supplement assembly remain with qt-d-1317-supplements.

Source: Aschbacher–Smith, proof of 13.1.9, printed pp.870–871; GLS, Number 2,
G.26.18(a), printed pp.152–153.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The GLS local configuration is impossible inside the literal XR.
Its selection is the remaining source step; no rank, characteristic-two,
3-prime, envelope, or representation obstruction is assumed here. -/
theorem controlledIndex_local_factorization_obstruction (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (Q N B A I : Subgroup G) [(I.subgroupOf N).Normal]
    (hB : B ∈ thompsonFamily (radicalSylowCentralizer T L) 1)
    (hBQ : B ≤ Q) (hQR : Q ≤ radicalSylowCentralizer T L) (hQN : Q ≤ N)
    (hNW : N ≤ XiP p L ⊔ radicalSylowCentralizer T L)
    (hNQ : N ≤ normalizer (Q : Set G))
    (hFQ : (XiP p L ⊔ radicalSylowCentralizer T L).pCoreIn 2 ≤ Q)
    (hSyl : IsSylowIn 2 Q I)
    (hBA : B ≤ A) (hA : A ∈ elementaryAbelianMaxSubgroups (radicalSylowCentralizer T L))
    (hAN : A ≤ N) (hne : ¬ A ≤ I)
    (Y : Subgroup (N ⧸ I.subgroupOf N)) [Y.Normal]
    {r : ℕ} [Fact r.Prime] (hYr : IsPGroup r Y) (hor : Odd r) (hYne : Y ≠ ⊥)
    (hmin : ∀ D : Subgroup (N ⧸ I.subgroupOf N), D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hCY : centralizer (Y : Set (N ⧸ I.subgroupOf N)) ≤ Y)
    (hcover : ¬ Y ≤ ((normalizer (omegaOneCenterAmbient
      (thompsonJ (radicalSylowCentralizer T L) 1) : Set G)).subgroupOf N).map
        (QuotientGroup.mk' (I.subgroupOf N))) : False := by
  let R := radicalSylowCentralizer T L
  let W := XiP p L ⊔ R
  have hr : 1 < twoRank R := lt_of_lt_of_le (by decide : 1 < 3)
    (controlledIndex_radical_rank h hL hn)
  have hQ : IsPGroup 2 Q := T.isPGroup'.to_le (hQR.trans (radicalSylowCentralizer_le _ _))
  have h3 : Nat.Coprime 3 (Nat.card N) :=
    (controlledIndex_XR_three_coprime h hL hn p ho hd).of_dvd_right
      (card_dvd_of_le hNW)
  have hF := controlledIndex_XR_generalizedFitting h hL hn p ho hd
  have hc : centralizer (pCore 2 W : Set W) ≤ pCore 2 W := by
    rw [←hF]
    exact centralizer_generalizedFitting_le W
  have hself : N ⊓ centralizer (Q : Set G) ≤ Q := by
    intro n hn
    have hw : (⟨n,hNW hn.1⟩ : W) ∈ centralizer (pCore 2 W : Set W) := by
      intro c hc
      exact Subtype.ext (hn.2 c (hFQ (mem_map_of_mem W.subtype hc)))
    exact hFQ (mem_map_of_mem W.subtype (hc hw))
  have hcore : N.pCoreIn 2 = Q :=
    pCoreIn_eq_of_normalized_sylow_and_coreFree_quotient N I Q hSyl hQN hNQ
      (twoCore_eq_bot_of_odd_minimal_selfCentralizing Y hYr hor hYne hmin hCY)
  have hEA : omegaOneCenterAmbient (thompsonJ R 1) ≤ A := by
    have hh := (lemma_B_2_3_2 R (show 0 ≤ 1 by omega) hr).1
    rw [(lemma_B_2_3_2 R (show 0 ≤ 1 by omega) hr).2,thompsonJ_zero] at hh
    apply hh.trans
    change thompsonAlpha R ≤ A
    rw [(lemma_B_2_3_7 R).2]
    exact sInf_le (by rwa [thompsonFamily_zero])
  exact factorization_local_obstruction R Q N B A I hr hB hBQ hQR hQ hQN hNQ
    hself hcore (hEA.trans hAN) hBA hA.2.1 hAN hne h3 Y hYr hor hYne hmin hCY hcover
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
