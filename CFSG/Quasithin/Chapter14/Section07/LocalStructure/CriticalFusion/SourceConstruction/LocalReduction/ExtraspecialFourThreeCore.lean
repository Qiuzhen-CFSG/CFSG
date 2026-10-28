module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourThree
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ThreeAutomorphisms
public import Theory.GroupTheory.TwoThreeSubnormalCore

/-!
# Vanishing of the original overgroup's quotient three-core

For each actual strict overgroup H ∩ C_G(x) < G₀ ≤ C_G(x), the quotient
G₀/O₂(G₀) has trivial three-core. If that core were nontrivial, the common
cubic and Sylow argument supplies a prime r > 3 dividing |G₀|. An element
of order r acts trivially on the quotient three-core by A.1.25(3). It
therefore normalizes X O₂(G₀) and its actual two-residual L₁, hence belongs
to H. This contradicts H's {2,3} prime support.

This proves the source three-core exclusion directly from the literal
quotient action, without an additional generalized-Fitting hypothesis.
Consequently every subnormal subgroup of G₀ lying in H is contained in
O₂(G₀). The original group, flag, central four-group, quotient maps and
earlier-source hypotheses are retained throughout.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed p.1053.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem extraspecial_H_prime_divisor
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card F.H) : r = 2 ∨ r = 3 := by
  have two_prime {A : Type u} [Group A] [Finite A] (hA : IsPGroup 2 A)
      (hdA : r ∣ Nat.card A) : r = 2 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn] at hdA
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdA)).resolve_left hr.ne_one
  have hcH := (pResidual 2 F.H).card_mul_index
  rw [←hcH] at hd
  rcases hr.dvd_mul.mp hd with hR | hQ
  · have hK : r ∣ Nat.card (K F) := by
      change r ∣ Nat.card ((pResidual 2 F.H).map F.H.subtype)
      rw [card_map_of_injective F.H.subtype_injective]
      exact hR
    have hcK := (pCore 2 (K F)).card_mul_index
    rw [←hcK] at hK
    rcases hr.dvd_mul.mp hK with hcore | hquot
    · exact Or.inl (two_prime (pCore_isPGroup (p := 2) (G := K F)) hcore)
    · obtain ⟨e⟩ := he
      change r ∣ Nat.card ((K F) ⧸ pCore 2 (K F)) at hquot
      rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card] at hquot
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hr.dvd_of_dvd_pow hquot)).resolve_left hr.ne_one)
  · change r ∣ Nat.card (F.H ⧸ pResidual 2 F.H) at hQ
    exact Or.inl (two_prime (isPGroup_quotient_pResidual (G := F.H) 2) hQ)

/-- The actual quotient of every strict outside-centralizer overgroup by
its two-core has trivial three-core. A prime greater than three supplied
by Sylow control acts trivially on that core by A.1.25(3), hence normalizes
X O₂(G₀) and its actual two-residual L₁, contradicting H's prime support. -/
theorem extraspecial_four_threeCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G)) :
    pCore 3 (G₀ ⧸ pCore 2 G₀) = ⊥ := by
  by_contra hthree
  obtain ⟨r,hr,hrbig,hrG⟩ := extraspecial_four_threeCore_large_prime
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' r hrG
  obtain ⟨Y,hYK,_,_,_,_,_,hres,_⟩ := extraspecial_four_threeCore_point_reconstruction
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  let Q := G₀.pCoreIn 2
  let X := Y ⊓ F.Li L 1
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let R := pCore 3 (G₀ ⧸ pCore 2 G₀)
  have hLI := (extraspecial_four_threeCore_point d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hx hxZ G₀ hJG.le hGC hthree).1
  have hXG : X ≤ G₀ := (inf_le_right.trans hLI).trans (map_subtype_le _)
  let X₀ := X.subgroupOf G₀
  have hXR : X₀.map q ≤ R := by
    rintro _ ⟨b,hb,rfl⟩
    obtain ⟨c,hc,hce⟩ := hLI (show (b : G) ∈ F.Li L 1 from hb.2)
    exact (show c = b from Subtype.ext hce) ▸ hc
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : primeRank 3 G₀ ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hGC) (inclusion_injective hGC)).trans
      (hC.stronglyQuasithin 3 (by decide) (by decide))
  have hR : primeRank 3 R ≤ 2 := (primeRank_subgroup_le 3 R).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G₀) pCore_isPGroup).trans hG)
  let f : G₀ →* MulAut R := (MulAut.conjNormal : (G₀ ⧸ pCore 2 G₀) →* MulAut R).comp q
  have hfa : f a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes
      ((hr.coprime_iff_not_dvd).mpr (fun hd => by
        have hh := ChapterA.lemma_A_1_25_3 pCore_isPGroup hR hr hd
        omega))
    · exact ha ▸ orderOf_map_dvd f a
    · exact orderOf_dvd_natCard _
  have hcent : q a ∈ centralizer (X₀.map q : Set (G₀ ⧸ pCore 2 G₀)) := by
    intro b hb
    have hh := congrArg (fun z : MulAut R => (z ⟨b,hXR hb⟩ : G₀ ⧸ pCore 2 G₀)) hfa
    change q a * b * (q a)⁻¹ = b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hnorm : a ∈ normalizer ((X₀ ⊔ pCore 2 G₀ : Subgroup G₀) : Set G₀) := by
    have hh := le_normalizer_comap q
      (show a ∈ (normalizer (X₀.map q : Set (G₀ ⧸ pCore 2 G₀))).comap q from
        Subgroup.centralizer_le_normalizer _ hcent)
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hnormG : (a : G) ∈ normalizer ((Q ⊔ X : Subgroup G) : Set G) := by
    have hh := (X₀ ⊔ pCore 2 G₀).le_normalizer_map G₀.subtype
      (mem_map_of_mem G₀.subtype hnorm)
    rw [Subgroup.map_sup,show X₀.map G₀.subtype = X from map_subgroupOf_eq_of_le hXG,
      show (pCore 2 G₀).map G₀.subtype = Q from rfl,sup_comm X Q] at hh
    exact hh
  have haL : (a : G) ∈ normalizer (F.Li L 1 : Set G) := by
    rw [←hres]
    exact normalizer_le_normalizer_characteristic_image (Q ⊔ X) (pResidual 2 _) hnormG
  have hNL : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans
      (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have haH : (a : G) ∈ F.H := hNL ▸ haL
  have horder : orderOf (⟨a,haH⟩ : F.H) = r := by
    exact (orderOf_injective F.H.subtype F.H.subtype_injective _).symm.trans
      ((orderOf_injective G₀.subtype G₀.subtype_injective a).trans ha)
  have hh := extraspecial_H_prime_divisor he hr (horder ▸ orderOf_dvd_natCard (⟨a,haH⟩ : F.H))
  omega
/-- O₂(G₀) contains every subnormal subgroup of the actual overgroup lying in H. -/
theorem extraspecial_four_subnormal_le_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (J : Subgroup G) (hJH : J ≤ F.H) (hJG₀ : J ≤ G₀)
    (hsub : (J.subgroupOf G₀).IsSubnormal) : J ≤ G₀.pCoreIn 2 := by
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hh := le_twoCore_of_subnormal_two_three h3 (J.subgroupOf G₀) hsub (by
    intro p hp hd
    have hcardJ : Nat.card (J.subgroupOf G₀) = Nat.card J :=
      Nat.card_congr (subgroupOfEquivOfLe hJG₀).toEquiv
    rw [hcardJ] at hd
    exact extraspecial_H_prime_divisor he hp (hd.trans (card_dvd_of_le hJH)))
  change J ≤ (pCore 2 G₀).map G₀.subtype
  simpa only [map_subgroupOf_eq_of_le hJG₀] using map_mono (f := G₀.subtype) hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
