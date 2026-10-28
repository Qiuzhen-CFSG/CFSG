module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBounds
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalFiniteExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBinaryExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryHeld
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringClosure
public import Theory.GroupTheory.CentralQuotientLocalEmbedding

/-!
# Excluding the full Held component in an odd-kernel normalizer

The local residual has centerless quotient isomorphic to two copies of the
original seed quotient. Its kernel in the component's central quotient is
central and a two-group, hence trivial when the component has trivial two-core.
The actual local module has order at least 64, while the paired seed quotient
has order divisible by 64. Held's native Sylow order bound excludes this
embedding. Covering uniqueness and outer solvability discharge residual
placement for the original elementary Hall kernel.

The full component center and the original subgroup maps are retained.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), printed pp.621--623,745.
Only fixation of the displayed local module is required.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual local residual cannot lie in a zero-two-core Held cover. -/
theorem source_nonnormal_oddNormalizer_no_placed_held_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (e : K ⧸ center K ≃* Held.He) : False := by
  let Q := L ⧸ pCore 2 L
  let := D.quasisimple
  have hzQ : center Q = ⊥ := source_nonnormal_component_core_center D hn
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : IsSimpleGroup Q := ((QuotientGroup.quotientMulEquivOfEq hzQ).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup
  let N := normalizer (B : Set G)
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let P := (F.subgroupOf N).subgroupOf K
  let W := (V.subgroupOf N).subgroupOf K
  obtain ⟨_,_,_,_,hW,hWP,_,_,⟨a⟩⟩ :=
    source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
  obtain ⟨b⟩ := source_nonnormal_orbit_product_equiv D hn
  have hzP : center (P ⧸ pCore 2 P) = ⊥ := by
    apply bot_unique
    intro z hz
    have hz' := (centerCongr (a.trans b) ⟨z,hz⟩).property
    change (a.trans b) z ∈ center (Q × Q) at hz'
    rw [Subgroup.center_prod,hzQ,bot_prod_bot,mem_bot] at hz'
    exact (a.trans b).map_eq_one_iff.mp hz'
  let q := QuotientGroup.mk' (center K)
  let f : P →* Held.He := e.toMonoidHom.comp (q.comp P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    apply CentralQuotientLocalMarking.subgroupMap_injective_of_twoCore_eq_bot P hzP hc
    apply Subtype.ext
    exact e.injective he
  have hPd : Nat.card P ∣ Nat.card Held.He := card_dvd_of_injective f hf
  have hcard : Nat.card P = Nat.card Q^2 * Nat.card (pCore 2 P) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 P),
      Nat.card_congr (a.trans b).toEquiv,Nat.card_prod,pow_two]
  have hQdvd : Nat.card Q^2 ∣ Nat.card Held.He :=
    (show Nat.card Q^2 ∣ Nat.card P by rw [hcard]; exact dvd_mul_right _ _).trans hPd
  have hVN : V ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVK : V.subgroupOf N ≤ K := by
    obtain ⟨_,_,hVF⟩ := source_local_oddActor_cover D V hVV hVX hNV B hBC hodd hBV
    exact (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
  let c : W ≃* V :=
    (subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)
  have hcardV : Nat.card V ≤ 2^6 := by
    rw [←Nat.card_congr c.toEquiv]
    exact elementary_card_le_of_twoCore_eq_bot W hW hc
      ((primeRank_congr 2 e).trans_le Held.primeRank_two_le_six)
  let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVV
  have h5 : ¬ 5 ∣ Nat.card Q := by
    intro hd
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hup : primeRank 5 (MulAut V) ≤ 1 := by
      apply primeRank_le_one_of_square_not_dvd
      obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
      have hb : d ≤ 6 := by
        rw [hd] at hcardV
        exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcardV
      rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V d hd]
      interval_cases d <;> norm_num [Fin.prod_univ_succ]
    have hlo := source_local_automorphism_rank D hn V hVV hne hVX hNV (by decide : Odd 5)
    have hpos : 0 < primeRank 5 Q := Nat.pos_of_ne_zero
      (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd)
    change 2 * primeRank 5 Q ≤ primeRank 5 (MulAut V) at hlo
    omega
  have h8 : 8 ∣ Nat.card Q := by
    by_contra hn8
    have hgraph := Held.NormalizerGraph.Orbital.held_le_preservingGroup
    have hHe := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hgraph
      (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hgraph)
    have hsmall := held_square_order_bound Nat.card_pos.ne' (hQdvd.trans hHe)
    have hco : Nat.Coprime (Nat.card Q) 5 :=
      ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5).symm
    have h1344 : Nat.card Q ∣ 1344 := hco.dvd_mul_right.mp hsmall
    exact no_simple_perfect_order_84 Q
      (dvd_eightyFour_of_dvd_thirteenFortyFour Nat.card_pos.ne' h1344 hn8)
  have h64 : 2^6 ∣ Nat.card V :=
    elementary_sixtyFour_dvd_of_doubled_odd_ranks Q V (fun p hp ho => by
      let : Fact p.Prime := ⟨hp⟩
      exact source_local_automorphism_rank D hn V hVV hne hVX hNV ho)
  have hcore : 2^6 ∣ Nat.card (pCore 2 P) := by
    rw [←Nat.card_congr c.toEquiv] at h64
    have hd := h64.trans (card_dvd_of_le hWP)
    change 2^6 ∣ Nat.card (P.pCoreIn 2) at hd
    simpa only [pCoreIn,card_map_of_injective P.subtype_injective] using hd
  have hlarge : 2^12 ∣ Nat.card P := by
    rw [hcard]
    have hh := Nat.mul_dvd_mul (pow_dvd_pow_of_dvd h8 2) hcore
    norm_num at hh ⊢
    exact hh
  exact Held.not_two_pow_twelve_dvd_card (hlarge.trans hPd)


end CFSG.Quasithin.Chapter10.LocalFixed
