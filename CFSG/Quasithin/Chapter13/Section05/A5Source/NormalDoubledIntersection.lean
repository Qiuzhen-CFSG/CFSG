module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPointSplit
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The common ordinary overlap inside the doubled normal A5 pair

Write J=O²(H)V and B=L₁T. The point centralizer C_L(V₁) is L₁V:
the normal residual L₁ has order 96, and the marked involution in V
outside O²(H) doubles it. This subgroup lies in B∩J and has order 192.
The order of B∩J divides both |B| (192 or 384) and |J|=576, forcing
equality. Thus restricting the source point endpoint to J and the plane
endpoint to L gives the same literal overlap in both embeddings.

This is the ordinary-subamalgam intersection step used in the doubled branch
of Aschbacher--Smith 13.5.17, printed p.922. It retains the original Context
and applies to both alternatives of 13.5.15(8).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

omit hA312 hU hn [IsElementaryAbelian 2 V] in
/-- The plane restriction of the original Borel is its point centralizer. -/
theorem normal_borel_inf_local :
    (residualCentralizer L V₁ ⊔ (T : Subgroup G)) ⊓ L =
      L ⊓ centralizer (V₁ : Set G) := by
  apply le_antisymm
  · exact le_inf inf_le_right (inf_le_left.trans (hH.1.2.trans hH.2.1))
  · refine le_inf ?_ inf_le_left
    rw [← d.borel_eq_point_centralizer]
    exact le_sup_left.trans d.borel_sup_sylow_eq_residual_sup_sylow.le

/-- The original plane point centralizer has order 192. -/
theorem normal_point_centralizer_card :
    Nat.card (L ⊓ centralizer (V₁ : Set G) : Subgroup G) = 192 := by
  have hc := ((L ⊓ centralizer (V₁ : Set G)).subgroupOf L).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (inf_le_left : L ⊓ centralizer (V₁ : Set G) ≤ L)).toEquiv] at hc
  change Nat.card (L ⊓ centralizer (V₁ : Set G) : Subgroup G) *
    (L ⊓ centralizer (V₁ : Set G)).relIndex L = Nat.card L at hc
  rw [d.point_centralizer_relIndex, normal_local_card d hA312 hH hU hn] at hc
  omega

/-- Normality makes the residual two-core the whole quaternion point core,
so its cubic quotient fixes the residual order. -/
theorem normal_residual_card : Nat.card (residualCentralizer L V₁) = 96 := by
  have hQL : Source.QH H ≤ residualCentralizer L V₁ := by
    rw [normal_core_eq_closure d hA312 hH hU hn]
    exact (normal_closure_reduction d hA312 hH hn).2.1.trans (pCoreIn_le 2 _)
  have he : (residualCentralizer L V₁).pCoreIn 2 = Source.QH H := by
    rw [← normal_residual_core_intersection d hA312 hH hn]
    exact inf_eq_right.mpr hQL
  obtain ⟨q, _⟩ := normal_point_core_geometry d hA312 hH hU hn
  have hcard : Nat.card (pCore 2 (residualCentralizer L V₁)) = 32 := by
    rw [← card_map_of_injective (K := pCore 2 (residualCentralizer L V₁))
      (residualCentralizer L V₁).subtype_injective]
    change Nat.card ((residualCentralizer L V₁).pCoreIn 2) = 32
    rw [he]
    exact (card_map_of_injective H.subtype_injective).trans q.card
  have hc := (pCore 2 (residualCentralizer L V₁)).card_mul_index
  rw [hcard, index_eq_card, residual_quotient_card d hA312 hH hU] at hc
  omega

omit hA312 hU hn [IsElementaryAbelian 2 V] in
/-- The original centralizer residual lies in the embedded point residual. -/
theorem normal_residual_le_point_residual :
    residualCentralizer L V₁ ≤ (pResidual 2 H).map H.subtype := by
  apply embedded_pResidual_mono 2
  rw [← normal_borel_inf_local d hH]
  exact inf_le_left.trans hH.1.2

/-- The original module supplements the residual to the ordinary overlap. -/
theorem normal_residual_sup_module_eq_centralizer :
    residualCentralizer L V₁ ⊔ V = L ⊓ centralizer (V₁ : Set G) := by
  have hVL : V ≤ L := d.chosen.le_componentCore.trans (pCoreIn_le 2 L)
  have hVC : V ≤ L ⊓ centralizer (V₁ : Set G) := by
    rw [← normal_borel_inf_local d hH]
    exact le_inf (d.chosen.le_sylow.trans le_sup_right) hVL
  have hle : residualCentralizer L V₁ ⊔ V ≤ L ⊓ centralizer (V₁ : Set G) :=
    sup_le ((map_subtype_le _)) hVC
  obtain ⟨v, hv, hv2, hvr⟩ := normal_source_point_involution d hA312 hH hU hn
  have hout : (v : G) ∉ residualCentralizer L V₁ := by
    intro hx
    exact hvr ((mem_map_iff_mem H.subtype_injective).mp
      (normal_residual_le_point_residual d hH hx))
  have hnorm : (v : G) ∈ normalizer (residualCentralizer L V₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hH.1.2)).mp hn v.property
  have hc := card_sup_zpowers_of_normalizing_involution (residualCentralizer L V₁)
    (v : G) (congrArg Subtype.val hv2) hout hnorm
  rw [normal_residual_card d hA312 hH hU hn] at hc
  apply eq_of_le_of_card_ge hle
  rw [normal_point_centralizer_card d hA312 hH hU hn]
  have hb := card_le_of_le (sup_le_sup_left (zpowers_le.mpr hv)
    (residualCentralizer L V₁))
  rw [hc] at hb
  exact hb

/-- The embedded ordinary point subgroup keeps the order of its intrinsic
construction in H. -/
theorem normal_point_subgroup_ambient_card :
    Nat.card ((pResidual 2 H).map H.subtype ⊔ V : Subgroup G) = 576 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨_, _, _, _, _, _, hc⟩ := normal_point_split_subgroup d hA312 hH hU hn
  have he : (pResidual 2 H ⊔ V.subgroupOf H).map H.subtype =
      (pResidual 2 H).map H.subtype ⊔ V := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hf.V_le_H]
  rw [← he, card_map_of_injective H.subtype_injective]
  exact hc

/-- Restricting the actual Borel to the ordinary point subgroup and to L
gives exactly the same subgroup, with no doubled-case hypothesis required. -/
theorem normal_point_subgroup_overlap :
    (residualCentralizer L V₁ ⊔ (T : Subgroup G)) ⊓
        ((pResidual 2 H).map H.subtype ⊔ V) =
      (residualCentralizer L V₁ ⊔ (T : Subgroup G)) ⊓ L := by
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let J := (pResidual 2 H).map H.subtype ⊔ V
  have hC : L ⊓ centralizer (V₁ : Set G) ≤ B ⊓ J := by
    rw [← normal_residual_sup_module_eq_centralizer d hA312 hH hU hn]
    exact le_inf (sup_le le_sup_left (d.chosen.le_sylow.trans le_sup_right))
      (sup_le_sup (normal_residual_le_point_residual d hH) le_rfl)
  have hcJ : Nat.card J = 576 := normal_point_subgroup_ambient_card d hA312 hH hU hn
  have hdB : Nat.card (B ⊓ J : Subgroup G) ∣ Nat.card B := card_dvd_of_le inf_le_left
  have hdJ : Nat.card (B ⊓ J : Subgroup G) ∣ 576 := hcJ ▸ card_dvd_of_le inf_le_right
  have hd : Nat.card (B ⊓ J : Subgroup G) ∣ 192 := by
    rcases normal_local_orders d hA312 hH hU hn with hc | hc
    · exact hc.2.1 ▸ hdB
    · have hh := Nat.dvd_gcd (hc.2.1 ▸ hdB) hdJ
      norm_num at hh
      exact hh
  have he : L ⊓ centralizer (V₁ : Set G) = B ⊓ J :=
    eq_of_le_of_card_ge hC (by
      rw [normal_point_centralizer_card d hA312 hH hU hn]
      exact Nat.le_of_dvd (by decide) hd)
  exact he.symm.trans (normal_borel_inf_local d hH).symm

/-- The two ordinary endpoints themselves intersect in that same original
point centralizer, ready for the restricted source amalgam. -/
theorem normal_point_subgroup_inf_local :
    ((pResidual 2 H).map H.subtype ⊔ V) ⊓ L =
      L ⊓ centralizer (V₁ : Set G) := by
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let J := (pResidual 2 H).map H.subtype ⊔ V
  have hJH : J ≤ H := sup_le (map_subtype_le _)
    (d.chosen.le_sylow.trans (le_sup_right.trans hH.1.2))
  have he : J ⊓ L = B ⊓ J := by
    apply le_antisymm
    · intro x hx
      refine ⟨?_, hx.1⟩
      change x ∈ residualCentralizer L V₁ ⊔ (T : Subgroup G)
      rw [← normal_local_intersection d hA312 hH hU hn]
      exact ⟨hJH hx.1, mem_sup_left hx.2⟩
    · intro x hx
      have hh : x ∈ B ⊓ L := (normal_point_subgroup_overlap d hA312 hH hU hn) ▸ hx
      exact ⟨hx.2, hh.2⟩
  exact he.trans ((normal_point_subgroup_overlap d hA312 hH hU hn).trans
    (normal_borel_inf_local d hH))

end CFSG.Quasithin.Chapter13.Section05.A5Source
