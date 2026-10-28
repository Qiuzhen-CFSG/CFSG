module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceCount.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.OddNormalizer
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Nilpotent

/-!
# The original root product and torus fixed subgroup

In the notation of GLS IV, Chapter 2, Lemma 15.6, write A=M°, U=O₂(J),
and V=O₂(M), retaining their actual images in the ambient group. The root
product AU has order q|U|. A nonidentity torus element fixes exactly U in
AU and in V: its centralizer in V is a two-group in which U is
self-normalizing, by (15E) and (15F). The normalizer condition forces equality.
The product formula for VD also bounds |V| by q³|U| without assuming M=VD.

Source: refs/KGroup/GLS4/Chapter2.tex, Lemma 15.6, lines 2718–2724.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory PFAppendixIII
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "L" => residualGenerated M z t
local notation "J" => centralizer (L : Set G)
local notation "D" => residualPairStabilizer M t
local notation "K" => residualCommutator M t
local notation "V" => pointCore M
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

omit [Finite G] in
public theorem point_normalizes_pointCore : M ≤ normalizer (V : Set G) := by
  simpa only [pointCore, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pCore 2 M).le_normalizer_map M.subtype

include d

public theorem distinguished_disjoint_twoCore : Disjoint A U := by
  apply disjoint_def.mpr
  intro a ha hu
  by_contra hne
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  have hi : PFAppendixIII.IsInvolution a := ⟨hne, elemPow_eq_one_of_isElementaryAbelian a ha⟩
  have hzA := (isInvolution_iff_mem_Z_in_proper_residualGenerated
    d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
    d.proper (d.distinguished_le ha)).mp hi
  exact not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected
    d.t_not_mem_M (centralizer_residualGenerated_le_pair d.minimal.disconnected
      d.z_mem d.z_mem_M (map_subtype_le _ hu)) hzA

public theorem twoCore_centralizes_distinguished : U ≤ centralizer (A : Set G) :=
  (map_subtype_le _).trans (centralizer_le d.distinguished_le)

public theorem sup_card : Nat.card (A ⊔ U : Subgroup G) = 2 ^ n * Nat.card U := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A U
    ((twoCore_centralizes_distinguished d).trans (Subgroup.centralizer_le_normalizer _))
    (distinguished_disjoint_twoCore d), d.distinguished_elementary_card.2]

public theorem torus_centralizes_twoCore : K ≤ centralizer (U : Set G) := by
  apply le_centralizer_iff.mp
  exact (map_subtype_le _).trans (centralizer_le (show K ≤ L by
    rw [d.torus_structure.1]; exact inf_le_right))

public theorem torus_centralizer_sup {k : G} (hk : k ∈ K) (hkne : k ≠ 1) :
    (A ⊔ U) ⊓ centralizer ({k} : Set G) = U := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (A : Set G) * (U : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A U
        ((twoCore_centralizes_distinguished d).trans (Subgroup.centralizer_le_normalizer _))]
      exact hx.1
    obtain ⟨a, ha, v, hv, rfl⟩ := hp
    have hkV : Commute k v := (mem_centralizer_iff.mp (torus_centralizes_twoCore d hk) v hv).symm
    have hkA : Commute k a := by
      have hh := (mem_centralizer_singleton_iff.mp hx.2).symm
      change k * (a * v) = (a * v) * k at hh
      rw [mul_assoc a v k, ← hkV.eq, ← mul_assoc, ← mul_assoc] at hh
      exact mul_right_cancel hh
    have ha1 : a = 1 := by
      by_contra hane
      let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
      have hzA := (isInvolution_iff_mem_Z_in_proper_residualGenerated
        d.minimal.disconnected d.reduction d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M
        d.proper (d.distinguished_le ha)).mp
          ⟨hane, elemPow_eq_one_of_isElementaryAbelian a ha⟩
      have hc : a ∈ centralizerClosure Z k := subset_closure
        ⟨hzA, mem_centralizer_singleton_iff.mpr hkA.symm⟩
      rw [d.torus_centralizerClosure_eq_bot hk hkne] at hc
      exact hane hc
    change a * v ∈ U
    rw [ha1, one_mul]
    exact hv
  · exact le_inf le_sup_right (fun v hv => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (torus_centralizes_twoCore d hk) v hv))

/-- The nilpotent normalizer condition strengthens the source fixed-subgroup
calculation to the whole point two-core. -/
public theorem torus_centralizer_pointCore (hs : CentralizerLocalTwoData d)
    {k : G} (hk : k ∈ K) (hkne : k ≠ 1) :
    V ⊓ centralizer ({k} : Set G) = U := by
  let C := V ⊓ centralizer ({k} : Set G)
  have hUC : U ≤ C := le_inf (twoCore_le_pointCore d hs)
    (fun v hv => mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (torus_centralizes_twoCore d hk) v hv))
  have hC : IsPGroup 2 C := ((pCore_isPGroup (p := 2) (G := M)).map M.subtype).to_le inf_le_left
  let : Group.IsNilpotent C := hC.isNilpotent
  have hn : normalizer ((U).subgroupOf C : Set C) = (U).subgroupOf C := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hUC]
    intro c hc
    have hs : (c : G) ∈ A ⊔ U := pointCore_inf_twoCore_normalizer d hs ▸
      (show (c : G) ∈ V ⊓ normalizer (U : Set G) from ⟨c.property.1, hc⟩)
    exact torus_centralizer_sup d hk hkne ▸ ⟨hs, c.property.2⟩
  have he := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := C)) _ hn
  exact le_antisymm (subgroupOf_eq_top.mp he) hUC

public theorem pointCore_card_upper (hs : CentralizerLocalTwoData d) :
    Nat.card V ≤ (2 ^ n) ^ 3 * Nat.card U := by
  have hDV : D ≤ normalizer (V : Set G) := inf_le_left.trans point_normalizes_pointCore
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes V D hDV
  have hi : V ⊓ D = U := by
    rw [inf_comm]
    exact hs.pair_core_eq
  rw [hi] at hp
  have hb : Nat.card (V ⊔ D : Subgroup G) ≤ Nat.card M :=
    card_le_of_le (sup_le (map_subtype_le _) inf_le_left)
  have hm := linear_stabilizer_card_of_degree d.action d.t_not_mem_M d.degree_and_fixed.1
  have he : Nat.card V * Nat.card D ≤ ((2 ^ n) ^ 3 * Nat.card U) * Nat.card D := by
    rw [hp]
    calc
      _ ≤ Nat.card U * Nat.card M := Nat.mul_le_mul_left _ hb
      _ = _ := by rw [hm]; ac_rfl
  exact Nat.le_of_mul_le_mul_right he Nat.card_pos

end BenderSuzuki.ZD.LinearExclusion.SourceCount
