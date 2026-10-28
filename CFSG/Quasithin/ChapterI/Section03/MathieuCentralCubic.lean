module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedRankTwoModels
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Symplectic
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.Source
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.NondefiningRank
public import Theory.GroupTheory.PerfectCentralCoverKernelLowerBound
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.CenteredCoverLocalRank

/-!
# The central cubic excludes all remaining proper overcomponents

The original cubic is central in its full centralizer, hence in every
containing component that contains its residual. Odd-prime symplectic
covers have two-primary center; ordinary odd G₂ covers are centerless;
binary and ordinary odd unitary-four covers have two-primary center.
The exceptional G₂(3) and PSU₄(3) quotients have no Mathieu section by
order. A centered McL cover has local three-rank at least three.

Thus a quasithin quasisimple component with central cubic cannot have a
faithful involution fixing an M₂₂ component in its central quotient.
The previously checked model exclusions and actual quotient isomorphisms
remain in use. The literal exterior application is
Hall.OddNormalizer.PushingUpComponentEquality.
Source: Aschbacher--Smith 4.2.13, printed p.612; A.2.19, p.41;
I.1.3--4 and the covering calculations cited by the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

private theorem not_three_dvd_of_twoGroup {P : Type*} [Group P] [Finite P]
    (h : IsPGroup 2 P) : ¬ 3 ∣ Nat.card P := by
  obtain ⟨n,hn⟩ := h.exists_card_eq
  rw [hn]
  exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

omit [Finite E] in
/-- The odd symplectic multiplier is C₂, excluding a central cubic. -/
theorem central_cubic_not_odd_symplectic (h3 : 3 ∣ Nat.card (center E))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSp (E ⧸ center E) 2 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
  let : Group.IsPerfect (ClassicalGroup.PSp 2 F) :=
    Group.IsPerfect.ofSurjective (centralQuotientCover e).surjective
  have hd := (centralQuotientCover e).kernel_card_dvd_universal
  rw [centralQuotientCover_ker] at hd
  have hc := Nat.card_congr
    (LieMultipliers.Symplectic.oddPrimeUniversalKernelEquivC2 F hp2 hF).toEquiv
  rw [hc] at hd
  have hh := h3.trans hd
  norm_num at hh

omit [Finite E] in
/-- Ordinary odd G₂ has trivial multiplier; the ternary model fails by order. -/
theorem central_cubic_not_odd_g2 (h3 : 3 ∣ Nat.card (center E))
    (h : HasMathieuFixedComponent (E ⧸ center E))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassificationModels.IsG2At (E ⧸ center E) p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  by_cases hs : p = 3
  · have hd := (h.of_mulEquiv e).card_dvd
    rw [Atlas.G2.card_Model,hF,hs] at hd
    norm_num at hd
  · have hp2 : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
    have hc := center_eq_bot_of_centralQuotientEquiv
      (Atlas.G2.MultiplierOrdinary.prime_universalProjection_ker_eq_bot hF
        (by have hh := hp.two_le; omega)) e
    rw [hc,Subgroup.card_bot] at h3
    norm_num at h3

/-- All binary unitary-four covers have two-primary center, including q = 2. -/
theorem central_cubic_not_binary_unitary_four (h3 : 3 ∣ Nat.card (center E))
    {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSU (E ⧸ center E) 4 (2 ^ n)) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  obtain ⟨b⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n (by omega) hF hconj
  have hk := Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.kernel_isTwoGroup_binary
    J n (by omega) hF hconj (centralQuotientCover (e.trans b))
  rw [centralQuotientCover_ker] at hk
  exact not_three_dvd_of_twoGroup hk h3

/-- The ordinary odd unitary-four center is a two-group; q = 3 fails by order. -/
theorem central_cubic_not_odd_unitary_four (h3 : 3 ∣ Nat.card (center E))
    (h : HasMathieuFixedComponent (E ⧸ center E))
    {p : ℕ} (hp : p.Prime) (hmers : ∃ b : ℕ, p + 1 = 2 ^ b)
    (hm : ClassicalGroup.IsPSU (E ⧸ center E) 4 p) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨b,hb⟩ := hmers
    have hb2 : b < 2 := by
      by_contra hn
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ b by omega)
      omega
    interval_cases b <;> norm_num at hb
  by_cases hs : p = 3
  · have hd := (h.of_mulEquiv e).card_dvd.trans
      (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.projective_card_dvd_generalLinear_order J
        (by simpa only [hs,Nat.reducePow] using hF))
    norm_num at hd
  · have hk := Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.center_isTwoGroup_of_quotient_equiv
      J hp (by have hh := hp.two_le; omega) hF hconj e
    exact not_three_dvd_of_twoGroup hk h3

/-- The original central cubic removes every remaining Lie family. -/
theorem central_cubic_proper_model_is_mcl [IsSimpleGroup (E ⧸ center E)]
    (h3 : 3 ∣ Nat.card (center E))
    (h : HasMathieuFixedComponent (E ⧸ center E))
    (hm : ChapterA.Section02.IsTheoremBModel (E ⧸ center E)) :
    Nonempty ((E ⧸ center E) ≃* Sporadic.LeechRelated.McL.Carrier) := by
  let : Group.IsPerfect (E ⧸ center E) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
  rcases h.proper_model_residue hm with ho | ⟨n,hn,hu⟩ | hmc
  · rcases ho with ⟨p,hp,ho,hs⟩ | ⟨p,hp,ho,hg⟩ | ⟨p,hp,hmers,hu⟩
    · exact (central_cubic_not_odd_symplectic h3 hp ho hs).elim
    · exact (central_cubic_not_odd_g2 h3 h hp ho hg).elim
    · exact (central_cubic_not_odd_unitary_four h3 h hp hmers hu).elim
  · exact (central_cubic_not_binary_unitary_four h3 hn hu).elim
  · exact hmc

end CFSG.Quasithin.ChapterI.MathieuPumpup

public section
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Subgroup Theory.GroupTheory
variable {E : Type*} [Group E] [Finite E] [IsQuasisimple E]

/-- Quasithinness and the original central cubic exclude every proper-model row. -/
theorem no_central_cubic_mathieu_fixed_component
    (hqt : IsQuasithin E) (h3 : 3 ∣ Nat.card (center E))
    (h : HasMathieuFixedComponent (E ⧸ center E))
    (hm : ChapterA.Section02.IsTheoremBModel (E ⧸ center E)) : False := by
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  obtain ⟨e⟩ := central_cubic_proper_model_is_mcl h3 h hm
  have hr := Sporadic.LeechRelated.McL.local_three_rank_of_center_divisible h3 e
  have hu := isQuasithin_iff_twoLocalPrimeRank.mp hqt 3 (by decide) (by decide)
  omega

end CFSG.Quasithin.ChapterI.MathieuPumpup
