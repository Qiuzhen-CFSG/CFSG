module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoLinear
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoBender
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The surviving original rank-two component models

Apply the genuine Theorem C to the selected simple subgroup of H-star.
The preceding original-source exclusions remove the alternating, odd
linear and Bender rows. The small binary PSL₃ endpoint has order 168,
and the actual PSL₄(2)-A₈ equivalence removes that binary linear row.
The original inverted-order argument restricts odd PSU₃ to fields three
and five. Every retained model remains an isomorphism of the same K-star.

The conclusion also retains the faithful original Sylow image inside
O₃(C/O₂(C)), where C is the literal centralizer of V-hat in X-hat. The
remaining unitary, nonlinear binary rank-two, PSL₅(2) and sporadic rows
still require exclusion there. Neither rank one, abelian point span
12.6.26, later local alternatives nor universal NaturalReduction follows
from this partial inspection.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, last paragraph.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- The binary linear-three row, including its field-two endpoint, is absent in rank two. -/
theorem SourceHypothesis.original_rank_two_not_binaryLinearThree
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) (n : ℕ) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 3 (2^n) := by
  by_cases hn2 : 2 ≤ n
  · exact S.original_selectedComponent_not_binaryLinear D hZ z hz hTV hTz hbound hns hH hn c a hn2
  rintro ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩
  let := hFfield
  let := hFfinite
  have hn1 : n = 1 := by
    have hsize := Finite.one_lt_card (α := F)
    rw [hF] at hsize
    have hn0 : n ≠ 0 := by intro he; simp [he] at hsize
    omega
  have hF2 : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 168 := by
    rw [Matrix.PSL3.LinearThree.card_projective,hF2]
    norm_num
  have hlow : primeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) ≤ 1 :=
    primeRank_le_one_of_square_not_dvd (by rw [hcard]; decide)
  have hrB : primeRank 3 (Nonabelian.Setup.star H c.K) = 2 :=
    c.three_rank_eq_star.symm.trans hr
  rw [primeRank_equiv 3 e] at hrB
  omega

include hz hTV hTz hbound hH hn a in
/-- Restrict Theorem C on the same original selected component, retaining the
rank-two intrinsic centralizer core needed to exclude the surviving rows. -/
theorem SourceHypothesis.original_rank_two_restricted_models
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (hr : primeRank 3 c.K = 2) :
    let B := Nonabelian.Setup.star H c.K
    let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
    let C := centralizer (U : Set a.action.range)
    2 ≤ primeRank 3 (pCore 3 (C ⧸ pCore 2 C)) ∧
      ((ClassicalGroup.IsPSU B 3 3 ∨ ClassicalGroup.IsPSU B 3 5) ∨
        (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel B f ∧
          ¬ ClassicalGroup.IsPSL B 3 (2^f)) ∨
        ClassicalGroup.IsPSL B 5 2 ∨ ChapterA.Section02.IsTheoremCSporadicModel B) := by
  classical
  let B := Nonabelian.Setup.star H c.K
  refine ⟨S.original_rank_two_centralizer_core_rank D hZ z hz hTV hTz hbound hH hn c a hTI hns hr,?_⟩
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  have hs := (S.original_star_sqtk D hZ z hz hH).subgroup B
  have hm := ChapterA.Section02.theoremC_knownSimple (G := B) inferInstance
    (Group.IsPerfect.not_isMulCommutative B) hs.stronglyQuasithin hs.isKGroup
  have hrB : primeRank 3 B = 2 := c.three_rank_eq_star.symm.trans hr
  cases hm with
  | alternating n hn8 he =>
      by_cases hn6 : 6 ≤ n
      · have hn678 : n = 6 ∨ n = 7 ∨ n = 8 := by omega
        rcases hn678 with rfl|hh
        · exact (S.original_selectedComponent_not_alternatingSix D hZ z hz hTz hH c a he).elim
        · exact (S.original_selectedComponent_not_alternatingSevenEight D hZ z hz hTV hTz
            hbound hH hn c a hh he).elim
      · obtain ⟨e⟩ := he
        have hcard : Nat.card (alternatingGroup (Fin n)) ∣ 120 := by
          have hd := (alternatingGroup (Fin n)).card_subgroup_dvd_card
          rw [Nat.card_perm,Nat.card_fin] at hd
          exact hd.trans (by simpa only [show Nat.factorial 5 = 120 from rfl] using
            Nat.factorial_dvd_factorial (show n ≤ 5 by omega))
        have hlow : primeRank 3 (alternatingGroup (Fin n)) ≤ 1 :=
          primeRank_le_one_of_square_not_dvd (fun hd => (by decide : ¬ 9 ∣ 120) (hd.trans hcard))
        rw [primeRank_equiv 3 e] at hrB
        omega
  | odd hm =>
      cases hm with
      | linear_two p n hp ho hn2 he =>
          exact (S.original_rank_two_not_smallDegreeLinearTwo D hZ z hz hTz hH c a hr hp hn2 he).elim
      | linear_three p hp ho he =>
          exact (S.original_rank_two_not_oddLinearThree D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hp ho he).elim
      | unitary_three p hp ho he =>
          have hc : center B = ⊥ := center_eq_bot_of_simple_perfect
          let e₀ : (B ⧸ center B) ≃* B :=
            (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
          have hp35 := S.original_selectedComponent_oddUnitaryThree_quotient_parameter
            D hZ z hz hTV hTz hbound hns hH hn c a hp ho (he.of_mulEquiv e₀)
          exact Or.inl (hp35.elim (fun hp => Or.inl (hp ▸ he)) (fun hp => Or.inr (hp ▸ he)))
  | bender hm =>
      exact (S.original_rank_two_not_bender D hZ z hz hTV hTz hbound hH hn c a hTI hns hr hm).elim
  | rank_two f hm =>
      exact Or.inr (Or.inl ⟨f,hm,
        S.original_rank_two_not_binaryLinearThree D hZ z hz hTV hTz hbound hH hn c a hns hr f⟩)
  | linear_binary n hn45 he =>
      rcases hn45 with rfl|rfl
      · obtain ⟨F,hFfield,hFfinite,hF,⟨e⟩⟩ := he
        let := hFfield
        let := hFfinite
        let := Fintype.ofFinite F
        let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
          simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
        exact (S.original_selectedComponent_not_alternatingSevenEight D hZ z hz hTV hTz hbound
          hH hn c a (Or.inr rfl)
          ⟨(e.trans (Atlas.fieldEquivPSL 4 eF)).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩).elim
      · exact Or.inr (Or.inr (Or.inl he))
  | sporadic hm => exact Or.inr (Or.inr (Or.inr hm))
end CFSG.Quasithin.Chapter12.Section06
