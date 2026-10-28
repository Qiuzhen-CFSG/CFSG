module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.Basic
public import Theory.Alternating.PrimeRank
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.GroupTheory.TwoByThreeDisplacement

/-!
# Local action and intersection steps for the two small rows of 8.2.9

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed p.720 (PDF p.737).

The marked A₅ quotient in 8.2.6 supplies both odd ranks. The subgroup
O₂(L_U)U is contained in the original Sylow two-subgroup and normalized by H,
so is contained in O₂(H). The actual commutator of B/U with L_U then controls
B's image in H/O₂(H). We transport the order-two/order-four dichotomy from
Basic using the literal inclusions of V and I in H.

The hypotheses on the commutator in N_G(U)/U are the two local module
calculations in the proof of 8.2.8: full commutator for the natural A₅ row,
and index two for the five-dimensional indecomposable row. These calculations
still need to be instantiated from the marked module identifications. This
module does not assert the E.2.2 exclusion of case (II) or n(H)=1.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- H-normalization and the common Sylow place O₂(L_U)U in O₂(H). -/
theorem localCore_join_le_parabolicCore (L H I U T : Subgroup G)
    (hgen : I ⊔ T = H) (hT : IsPGroup 2 T)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : T ≤ normalizer (L : Set G)) (hTU : T ≤ normalizer (U : Set G))
    (hQT : (localResidual L U).pCoreIn 2 ≤ T)
    (hUT : U ≤ T)
    (hcomm : ⁅localResidual L U,
      centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2) :
    (localResidual L U).pCoreIn 2 ⊔ U ≤
      H.pCoreIn 2 := by
  let K := localResidual L U
  have hHK : H ≤ normalizer (K : Set G) :=
    normalizes_localResidual_of_generation
      L H I T U hgen hIC hTL hTU hcomm
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [← hgen]
    exact sup_le (hIC.trans (centralizer_le_normalizer _)) hTU
  have hQ : H ≤ normalizer (K.pCoreIn 2 : Set G) :=
    hHK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hle : K.pCoreIn 2 ⊔ U ≤ T := sup_le hQT hUT
  apply le_pCoreIn_of_normalizes (hT.to_le hle)
    (hle.trans (hgen ▸ le_sup_right))
  exact (le_inf hQ hHU).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
/-- The reverse inclusion needed for the equality B = V ∩ O₂(H). -/
private theorem core_intersection_le_pair (V I H : Subgroup G) (hVI : V ≤ I) (hIH : I ≤ H) :
    V ⊓ H.pCoreIn 2 ≤ V ⊓ I.pCoreIn 2 := by
  refine le_inf inf_le_left ?_
  exact (le_inf inf_le_right (inf_le_left.trans hVI)).trans
    (pCoreIn_inf_le_of_normalizes (hIH.trans H.le_normalizer))

omit [Finite G] in
/-- Containment in the core and relative index two give case (I). -/
private theorem intersection_and_image_of_le_core (V B H : Subgroup G) (hVH : V ≤ H)
    (hBV : B ≤ V) (hindex : B.relIndex V = 2) (hBQ : B ≤ H.pCoreIn 2)
    (hQB : V ⊓ H.pCoreIn 2 ≤ B) :
    B = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  have he : B = V ⊓ H.pCoreIn 2 := le_antisymm (le_inf hBV hBQ) hQB
  refine ⟨he, ?_⟩
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have hmap := relIndex_map_map_of_injective (pCore 2 H) (V.subgroupOf H)
    H.subtype_injective
  rw [map_subgroupOf_eq_of_le hVH] at hmap
  rw [← hmap, ← inf_relIndex_left]
  change (V ⊓ H.pCoreIn 2).relIndex V = 2
  rwa [← he]

/-- The actual A₅ marking in both small rows supplies m₃(H), m₅(H) ≤ 1. -/
theorem odd_ranks_of_local_alternating_five (T : Sylow 2 G) (L M H I U : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIH : I ≤ H) (hIM : ¬ I ≤ M)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hcomm : ⁅localResidual L U,
      centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2)
    (e : (localResidual L U ⧸
      pCore 2 (localResidual L U)) ≃*
      alternatingGroup (Fin 5))
    (h3 : primeRank 3 (H ⊔ localResidual L U : Subgroup G) ≤ 2)
    (h5 : primeRank 5 (H ⊔ localResidual L U : Subgroup G) ≤ 2) :
    primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hz (p : ℕ) : Nat.Coprime p (Nat.card (center (alternatingGroup (Fin 5)))) := by
    rw [alternatingGroup.center_eq_bot (by simp), card_bot]
    exact Nat.coprime_one_right p
  constructor
  · apply odd_rank_le_one_of_local_model
      T L M H I U hH hIH hIM hIC hTL hTU hcomm (by decide) e (hz 3) _ h3
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 3 (by decide) (by decide)]
  · apply odd_rank_le_one_of_local_model
      T L M H I U hH hIH hIM hIC hTL hTU hcomm (by decide) e (hz 5) _ h5
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 5 (by decide) (by decide)]

/-- A subgroup of O₂(H) of index at most two in B bounds the literal image B⁺. -/
private theorem image_card_le_two_of_index (B H D : Subgroup G) (hBH : B ≤ H) (hDQ : D ≤ H.pCoreIn 2)
    (hd : D.relIndex B ≤ 2) :
    Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have he := relIndex_map_map_of_injective (pCore 2 H) (B.subgroupOf H)
    H.subtype_injective
  rw [map_subgroupOf_eq_of_le hBH] at he
  rw [← he]
  exact (relIndex_le_of_le_left (L := B) hDQ (by
    rw [relIndex, index_eq_card]
    exact Nat.card_pos.ne')).trans hd

omit [Finite G] in
/-- Transport a commutator index through the actual quotient kernel. -/
private theorem commutator_index_lift {Q : Type*} [Group Q] (f : G →* Q) (B K U : Subgroup G)
    (hk : f.ker = U) (hBU : U ≤ B)
    (hc : (⁅B.map f, K.map f⁆).relIndex (B.map f) = 2) :
    (⁅B, K⁆ ⊔ U).relIndex B = 2 := by
  rw [← map_commutator, relIndex_map_map, hk, sup_eq_left.mpr hBU] at hc
  exact hc

omit [Finite G] in
/-- Lift full generation by commutators modulo the specified kernel. -/
private theorem commutator_span_lift {Q : Type*} [Group Q] (f : G →* Q) (B K U : Subgroup G)
    (hk : f.ker = U) (hc : B.map f = ⁅B.map f, K.map f⁆) :
    B ≤ ⁅B, K⁆ ⊔ U := by
  rw [← hk, ← comap_map_eq, ← map_le_iff_le_comap, map_commutator]
  exact hc.le

/-- Apply Basic’s intrinsic dichotomy to the original inclusions I ≤ H and V ≤ I. -/
private theorem ambient_pair_intersection_alternatives (V I B H : Subgroup G) (hVI : V ≤ I) (hIH : I ≤ H)
    (hB : B = V ⊓ I.pCoreIn 2) (hi : B.relIndex V = 2)
    (hc : Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2) :
    (B = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2) ∨
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 4 := by
  have hVH := hVI.trans hIH
  have hBH : B ≤ H := hB ▸ inf_le_left.trans hVH
  have hVhIh : V.subgroupOf H ≤ I.subgroupOf H := subgroupOf_mono _ hVI
  have hmap : ((I.subgroupOf H).pCoreIn 2).map H.subtype = I.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup H.subtype,
      map_subgroupOf_eq_of_le hIH]
    have hk : H.subtype.ker = ⊥ := H.subtype.ker_eq_bot H.subtype_injective
    rw [hk]
    exact IsPGroup.of_subsingleton 2 _
  have hBh : B.subgroupOf H = V.subgroupOf H ⊓ (I.subgroupOf H).pCoreIn 2 := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hBH, map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hVH, hmap, hB]
  have hih : (B.subgroupOf H).relIndex (V.subgroupOf H) = 2 := by
    rw [relIndex_subgroupOf hVH, hi]
  have hh := pair_intersection_alternatives
    (V.subgroupOf H) (I.subgroupOf H) (B.subgroupOf H) hVhIh hBh hih hc
  rcases hh with hh | hh
  · left
    refine ⟨?_, hh.2⟩
    have hm := congrArg (fun D : Subgroup H => D.map H.subtype) hh.1
    rw [map_subgroupOf_eq_of_le hBH, map_inf _ _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hVH] at hm
    exact hm
  · exact Or.inr hh

/-- The literal image of X in N_G(U)/U. Containment in N_G(U) is retained
separately when lifting statements from this image. -/
@[expose] def localImage (U X : Subgroup G) :
    Subgroup (normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) :=
  (X.subgroupOf (normalizer (U : Set G))).map
    (QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))))

omit [Finite G] in
private theorem local_commutator_span (U B K : Subgroup G)
    (hBN : B ≤ normalizer (U : Set G)) (hKN : K ≤ normalizer (U : Set G))
    (hc : localImage U B = ⁅localImage U B, localImage U K⁆) :
    B ≤ ⁅B, K⁆ ⊔ U := by
  let N := normalizer (U : Set G)
  have hh := commutator_span_lift
    (QuotientGroup.mk' (U.subgroupOf N)) (B.subgroupOf N) (K.subgroupOf N)
    (U.subgroupOf N) (QuotientGroup.ker_mk' _) hc
  have hm := map_mono (f := N.subtype) hh
  rwa [map_subgroupOf_eq_of_le hBN, Subgroup.map_sup, map_commutator,
    map_subgroupOf_eq_of_le hBN, map_subgroupOf_eq_of_le hKN,
    map_subgroupOf_eq_of_le U.le_normalizer] at hm

omit [Finite G] in
private theorem local_commutator_index (U B K : Subgroup G)
    (hUB : U ≤ B) (hBN : B ≤ normalizer (U : Set G))
    (hKN : K ≤ normalizer (U : Set G))
    (hc : (⁅localImage U B, localImage U K⁆).relIndex (localImage U B) = 2) :
    (⁅B, K⁆ ⊔ U).relIndex B = 2 := by
  let N := normalizer (U : Set G)
  have hh := commutator_index_lift
    (QuotientGroup.mk' (U.subgroupOf N)) (B.subgroupOf N) (K.subgroupOf N)
    (U.subgroupOf N) (QuotientGroup.ker_mk' _) (subgroupOf_mono N hUB) hc
  have he := relIndex_map_map_of_injective
    (⁅B.subgroupOf N, K.subgroupOf N⁆ ⊔ U.subgroupOf N)
    (B.subgroupOf N) N.subtype_injective
  rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hBN,
    map_subgroupOf_eq_of_le hKN, map_subgroupOf_eq_of_le U.le_normalizer] at he
  exact he.trans hh

section LocalSetup
variable (T : Sylow 2 G) (L M H I V B U : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hIH : I ≤ H) (hIM : ¬ I ≤ M) (hVI : V ≤ I)
    (hB : B = V ⊓ I.pCoreIn 2)
    (hIC : I ≤ centralizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hQT : (localResidual L U).pCoreIn 2 ≤ (T : Subgroup G))
    (hUT : U ≤ (T : Subgroup G))
    (hcomm : ⁅localResidual L U, centralizer (U : Set G)⁆ ≤
      (localResidual L U).pCoreIn 2)

include hH hIH hIM hVI hB hIC hTL hTU hQT hUT hcomm

omit [Finite G] in
private theorem local_commutator_join_le_core :
    ⁅B, localResidual L U⁆ ⊔ U ≤ H.pCoreIn 2 := by
  have hBC : B ≤ centralizer (U : Set G) :=
    (hB ▸ inf_le_left).trans (hVI.trans hIC)
  have hb : ⁅B, localResidual L U⁆ ≤ (localResidual L U).pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hBC).trans hcomm
  exact (sup_le_sup_right hb U).trans
    (localCore_join_le_parabolicCore L H I U (T : Subgroup G)
      (join_eq_of_minimal_outside T M H I hH hIH hIM) T.isPGroup'
      hIC hTL hTU hQT hUT hcomm)

/-- The L₃(4) local action forces B ≤ O₂(H), B = V ∩ O₂(H), and |V⁺| = 2.
The rank-one quotient is exactly the V/B of 8.2.5. -/
theorem linear_row_intersection [IsElementaryAbelian 2 V]
    (hVB : Module.finrank (ZMod 2) (Additive (V ⧸ B.subgroupOf V)) = 1)
    (hact : localImage U B = ⁅localImage U B, localImage U (localResidual L U)⁆) :
    B ≤ H.pCoreIn 2 ∧ B = V ⊓ H.pCoreIn 2 ∧
      Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  have hBV : B ≤ V := hB ▸ inf_le_left
  have hspan := local_commutator_span U B (localResidual L U)
    ((hBV.trans (hVI.trans hIC)).trans (centralizer_le_normalizer _))
    ((localResidual_le L U).trans inf_le_right) hact
  have hBQ := hspan.trans (local_commutator_join_le_core T L M H I V B U
    hH hIH hIM hVI hB hIC hTL hTU hQT hUT hcomm)
  have hi : B.relIndex V = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, hVB, pow_one]
  refine ⟨hBQ, intersection_and_image_of_le_core V B H (hVI.trans hIH) hBV hi hBQ ?_⟩
  rw [hB]
  exact core_intersection_le_pair V I H hVI hIH

/-- The M₂₂ commutator index gives |B:B ∩ O₂(H)| ≤ 2 and the source's
order-two/order-four alternatives. No four-group exclusion is assumed. -/
theorem mathieu22_row_intersection_alternatives [IsElementaryAbelian 2 V]
    (hUB : U ≤ B)
    (hVB : Module.finrank (ZMod 2) (Additive (V ⧸ B.subgroupOf V)) = 1)
    (hact : (⁅localImage U B, localImage U (localResidual L U)⁆).relIndex
      (localImage U B) = 2) :
    Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 ∧
      ((B = V ⊓ H.pCoreIn 2 ∧
        Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2) ∨
        Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 4) := by
  have hBV : B ≤ V := hB ▸ inf_le_left
  have hidx := local_commutator_index U B (localResidual L U) hUB
    ((hBV.trans (hVI.trans hIC)).trans (centralizer_le_normalizer _))
    ((localResidual_le L U).trans inf_le_right) hact
  have hsmall := image_card_le_two_of_index B H (⁅B, localResidual L U⁆ ⊔ U)
    (hBV.trans (hVI.trans hIH))
    (local_commutator_join_le_core T L M H I V B U
      hH hIH hIM hVI hB hIC hTL hTU hQT hUT hcomm) hidx.le
  have hi : B.relIndex V = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, hVB, pow_one]
  exact ⟨hsmall, ambient_pair_intersection_alternatives V I B H hVI hIH hB hi hsmall⟩
end LocalSetup

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows
