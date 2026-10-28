module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Common
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.SpecificGroups.Janko1.OddCoverExclusion
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Theory.GroupTheory.PerfectCentralCoverSylowNine
public import Theory.Mathieu.SchurMultipliers.OddLocalPartialInversion
public import Theory.Mathieu.SchurMultipliers.FiniteCovers
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddPrimary
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Janko
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Held
public import Theory.SpecificGroups.Janko3.Multiplier
public import Theory.SpecificGroups.Janko3.ThreeCoverLocalLifts
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeCoverLocalLifts
public import CFSG.Quasithin.ChapterI.Section02.SporadicCoverLocalRank

/-!
# Odd central covers in the sporadic source cases

The actual perfect-cover bounds exclude Mathieu, Janko, Held, Rudvalis and
Higman–Sims quotients. M₂₂ uses its certified rank and the original A.2.14
center equation; J₃ uses the actual central-three-cover local subgroup.

Source: Aschbacher–Smith A.2.19, printed pp.40–41 (Case I and Case II).
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u
variable {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

public theorem false_of_twoGroup_center
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (h2 : IsPGroup 2 (center G)) : False :=
  h.center_ne_bot ih.theoremA (center_eq_bot_of_two_and_odd h.2.2.2.2.1 h.2.2.2.2.2.1 hP h2)

public theorem cover_j1
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* Janko1.Model) : False :=
  h.center_ne_bot ih.theoremA (Janko1.OddCover.center_eq_bot
    (twoCore_eq_bot_of_odd_center h.2.2.2.2.1 h.2.2.2.2.2.1 hP) e)

private lemma square_not_dvd_m22 (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) : ¬ r ^ 2 ∣ Nat.card _root_.Sporadic.Mathieu.M22 := by
  intro hd
  let : Fact r.Prime := ⟨hr⟩
  have hpd : r ∣ Nat.card _root_.Sporadic.Mathieu.M22 := (show r ∣ r ^ 2 by
    simpa only [pow_one] using pow_dvd_pow r (by decide : 1 ≤ 2)).trans hd
  have h := (_root_.Sporadic.Mathieu.m22_prime_dvd_order_iff r).mp hpd
  have h' : r = 5 ∨ r = 7 ∨ r = 11 := by omega
  rw [_root_.Sporadic.Mathieu.m22_order] at hd
  rcases h' with rfl | rfl | rfl <;> norm_num at hd

public theorem cover_m22
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M22) : False := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  have hd := (centralQuotientCover e).kernel_card_dvd_three_of_pCore_eq_bot
    (twoCore_eq_bot_of_odd_center h.2.2.2.2.1 h.2.2.2.2.2.1 hP)
    (by rw [_root_.Sporadic.Mathieu.m22_order]; norm_num) square_not_dvd_m22
  rw [centralQuotientCover_ker] at hd
  have hz : Nat.card (center G) = 3 :=
    (Nat.prime_three.eq_one_or_self_of_dvd _ hd).resolve_left
      (fun he => h.center_ne_bot ih.theoremA (Subgroup.card_eq_one.mp he))
  have hpdiv : p ∣ 3 := hz ▸ (hP.card_eq_or_dvd.resolve_left
    (fun he => h.center_ne_bot ih.theoremA (Subgroup.card_eq_one.mp he)))
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq h.2.2.2.2.1 Nat.prime_three).mp hpdiv
  subst p
  have hr := lemma_A_2_14_center h ih.theoremA hz
  rw [primeRank_equiv 3 e, _root_.Sporadic.Mathieu.m22_primeRank_three] at hr
  omega

public theorem cover_m11
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M11) : False := by
  apply false_of_twoGroup_center h ih hP
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.PartialInversionSource.m11_cover_kernel_isTwoGroup
      (centralQuotientCover e)

public theorem cover_m12
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M12) : False := by
  apply false_of_twoGroup_center h ih hP
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.m12_cover_kernel_isTwoGroup (centralQuotientCover e)

public theorem cover_m23
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M23) : False := by
  apply false_of_twoGroup_center h ih hP
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.PartialInversionSource.m23_cover_kernel_isTwoGroup
      (centralQuotientCover e)

public theorem cover_m24
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* _root_.Sporadic.Mathieu.M24) : False := by
  apply false_of_twoGroup_center h ih hP
  rw [← centralQuotientCover_ker e]
  exact
    _root_.Sporadic.Mathieu.SchurMultipliers.m24_cover_kernel_isTwoGroup (centralQuotientCover e)

public theorem cover_j2
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G))
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.J2.Carrier) : False :=
  false_of_twoGroup_center h ih hP
    (Theory.SpecificGroups.J2HSMultipliers.J2.source_center_isPGroup ⟨e⟩)

public theorem cover_j4
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* Janko4.Model) : False :=
  false_of_twoGroup_center h ih hP (Janko4.OddPrimary.source_center_isPGroup ⟨e⟩)

public theorem cover_he
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* Held.He) : False :=
  false_of_twoGroup_center h ih hP (Held.OddPrimary.source_center_isPGroup ⟨e⟩)

public theorem cover_ru
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* Rudvalis.Model) : False :=
  false_of_twoGroup_center h ih hP (Rudvalis.Multiplier.source_center_isPGroup ⟨e⟩)

public theorem cover_hs
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G))
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.HS.Carrier) : False := by
  apply h.center_ne_bot ih.theoremA
  exact Theory.SpecificGroups.J2HSMultipliers.HS.center_eq_bot_of_odd_pGroup_of_quotient_equiv
    e h.2.2.2.2.1 (by intro he; have ho := h.2.2.2.2.2.1; rw [he] at ho; norm_num at ho) hP

public theorem cover_j3
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hP : IsPGroup p (center G))
    (e : G ⧸ center G ≃* _root_.Sporadic.Janko3.Model) : False := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsQuasisimple (G ⧸ center G) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center G)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple _root_.Sporadic.Janko3.Model := IsQuasisimple.of_mulEquiv e
  have hp3 := _root_.Sporadic.Janko3.source_center_prime_eq_three e
    (by intro he; have ho := h.2.2.2.2.2.1; rw [he] at ho; norm_num at ho)
    hP (h.center_ne_bot ih.theoremA)
  subst p
  exact _root_.Sporadic.Janko3.not_quasithin_of_nontrivial_three_center hP
    (h.center_ne_bot ih.theoremA) e h.1

public theorem cover_mcl_of_three_center
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (h3 : IsPGroup 3 (center G))
    (e : G ⧸ center G ≃* _root_.Sporadic.LeechRelated.McL.Carrier) : False := by
  obtain ⟨Q,f,hQ,hQp,hf,hn⟩ := _root_.Sporadic.LeechRelated.McL.exists_three_cover_local_lift
    h3 (h.center_ne_bot ih.theoremA) e
  exact ChapterI.sporadicCover_not_quasithin_of_e9_lift h3 (h.center_ne_bot ih.theoremA)
    Q hQp hQ f hf hn h.1

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
