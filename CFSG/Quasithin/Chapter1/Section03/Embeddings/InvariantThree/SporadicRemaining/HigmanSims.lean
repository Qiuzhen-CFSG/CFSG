module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.NormalCoreIndexFactorial

/-!
# The HS Sylow-pair exclusion from concrete local calculations

The certified ambient order bound forces the odd complement R to have
order nine. If a Sylow two-subgroup S has order 512 and permutes with R,
the product RS has order 4608 and S has index nine in it. A trivial
two-core would embed RS in the symmetric group on nine letters, contrary
to divisibility of orders. Thus RS lies in a maximal two-local containing S.

The intrinsic normal elementary catalogue in the specified Sylow subgroup
identifies all such maximal locals with the three actual candidate
normalizers. Each normalizer has order indivisible by nine, as proved in
`LargeNormalizerThreePart` and `CentralNormalizerThreePart`. The checked
`SylowCatalogue` supplies the candidate order and exhaustive catalogue,
so `no_pair` discharges every model premise on the exact ATLAS carrier.
The required action exclusion follows. The proof uses no action
irreducibility conclusion, model comparison, or simplicity certificate.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing Asc86b; GLS volume 3, Table 5.3m, printed p.274.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HigmanSims
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.EvenLocalCandidates

/-- The extraspecial complement order is excluded by the actual carrier order bound. -/
public theorem complement_card {S : Sylow 2 Carrier} {R : Subgroup Carrier}
    (h : PairInput S R) : Nat.card R = 9 := by
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact hc
  · have hd := R.card_subgroup_dvd_card.trans card_carrier_dvd
    rw [hc] at hd
    norm_num at hd

/-- The product subgroup has a nontrivial intrinsic two-core by its coset action. -/
public theorem product_twoCore_ne_bot {S : Sylow 2 Carrier} {R : Subgroup Carrier}
    (h : PairInput S R) (hS : Nat.card S = 512) :
    pCore 2 (R ⊔ (S : Subgroup Carrier) : Subgroup Carrier) ≠ ⊥ := by
  let H := R ⊔ (S : Subgroup Carrier)
  let P := (S : Subgroup Carrier).subgroupOf H
  have hP : Nat.card P = 512 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show (S : Subgroup Carrier) ≤ H from le_sup_right)).toEquiv).trans hS
  have hH : Nat.card H = 9 * 512 := by
    rw [EvenRankTwo.product_card h, complement_card h, hS]
  have hi : P.index = 9 := by
    have he := P.card_mul_index
    rw [hP, hH] at he
    omega
  apply pCore_ne_bot_of_not_card_dvd_factorial_index P S.isPGroup'.comap_subtype
  rw [hH, hi]
  norm_num [Nat.factorial]

/-- Genuine two-local containment of RS, without an assumed local overgroup. -/
public theorem exists_maximalTwoLocal_overgroup {S : Sylow 2 Carrier}
    {R : Subgroup Carrier} (h : PairInput S R) (hS : Nat.card S = 512) :
    ∃ M : Subgroup Carrier, IsMaximalTwoLocal M ∧ R ⊔ (S : Subgroup Carrier) ≤ M :=
  exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot _ (product_twoCore_ne_bot h hS)

/-- The intrinsic catalogue gives literal equality with the full local normalizers. -/
public theorem exists_sylow_local_cover_of_catalogue
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcatalogue : ∀ A : Subgroup subgroup, A ≠ ⊥ → A.Normal →
      IsElementaryAbelian 2 A → ∃ i : Fin 3, A.map subgroup.subtype = elementary i) :
    ∃ T : Sylow 2 Carrier, Nat.card T = 512 ∧
      ∀ M : Subgroup Carrier, IsMaximalTwoLocal M → (T : Subgroup Carrier) ≤ M →
        ∃ i : Fin 3, M = localGroup i := by
  have hindex : ¬ 2 ∣ subgroup.index := by
    intro hi
    have hd : 1024 ∣ Nat.card Carrier := by
      rw [← subgroup.card_mul_index, hS]
      exact Nat.mul_dvd_mul_left 512 hi
    have := hd.trans card_carrier_dvd
    norm_num at this
  let T : Sylow 2 Carrier := (IsPGroup.of_card hS).toSylow hindex
  refine ⟨T, hS, ?_⟩
  intro M hM hTM
  exact maximalTwoLocal_eq_of_normal_elementary_catalogue T elementary hcatalogue hM hTM

/-- HS exclusion from the candidate order, exhaustive intrinsic catalogue,
and first local's three-part restriction. -/
public theorem no_pair_of_normal_elementary_catalogue
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcatalogue : ∀ A : Subgroup subgroup, A ≠ ⊥ → A.Normal →
      IsElementaryAbelian 2 A → ∃ i : Fin 3, A.map subgroup.subtype = elementary i)
    (hzero : ¬ 9 ∣ Nat.card (localGroup 0))
    {S : Sylow 2 Carrier} {R : Subgroup Carrier} (h : PairInput S R) : False := by
  obtain ⟨T, hT, hcover⟩ := exists_sylow_local_cover_of_catalogue hS hcatalogue
  have hfixed (P : Subgroup Carrier) (hP : PairInput T P) : False := by
    obtain ⟨M, hM, hPM⟩ := exists_maximalTwoLocal_overgroup hP hT
    obtain ⟨i, rfl⟩ := hcover M hM (le_sup_right.trans hPM)
    have hd : 9 ∣ Nat.card (localGroup i) := by
      rw [← complement_card hP]
      exact card_dvd_of_le (le_sup_left.trans hPM)
    by_cases hi : i = 0
    · exact hzero (hi ▸ hd)
    · exact large_localGroup_nine_not_dvd i hi hd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier S T
  have hh := pairInput_of_equiv h (MulAut.conj g)
  have hmap : S.mapSurjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective = T := by
    apply Sylow.ext
    change (g • S : Sylow 2 Carrier).toSubgroup = T.toSubgroup
    rw [hg]
  rw [hmap] at hh
  exact hfixed _ hh

/-- The action-exclusion interface follows from the same conditional no-pair theorem. -/
public theorem pairReducible_of_normal_elementary_catalogue
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcatalogue : ∀ A : Subgroup subgroup, A ≠ ⊥ → A.Normal →
      IsElementaryAbelian 2 A → ∃ i : Fin 3, A.map subgroup.subtype = elementary i)
    (hzero : ¬ 9 ∣ Nat.card (localGroup 0))
    {S : Sylow 2 Carrier} {R : Subgroup Carrier} (h : PairInput S R) :
    PairReducible (S : Subgroup Carrier) R :=
  (no_pair_of_normal_elementary_catalogue hS hcatalogue hzero h).elim

/-- No source input pair exists in the exact ATLAS Higman–Sims carrier.
All concrete order and coverage premises are discharged. -/
public theorem no_pair {S : Sylow 2 Carrier} {R : Subgroup Carrier}
    (h : PairInput S R) : False :=
  no_pair_of_normal_elementary_catalogue subgroup_card normal_elementary_catalogue
    central_localGroup_nine_not_dvd h

/-- The Higman–Sims branch of the Sylow-pair action exclusion. -/
public theorem pairReducible {S : Sylow 2 Carrier} {R : Subgroup Carrier}
    (h : PairInput S R) : PairReducible (S : Subgroup Carrier) R :=
  (no_pair h).elim

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HigmanSims
