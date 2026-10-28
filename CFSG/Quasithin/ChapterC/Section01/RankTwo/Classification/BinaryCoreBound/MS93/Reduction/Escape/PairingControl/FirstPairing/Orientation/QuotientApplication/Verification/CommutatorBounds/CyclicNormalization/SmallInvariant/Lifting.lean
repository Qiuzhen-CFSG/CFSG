module

public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Centralizer indices and lifting subgroup invariance

An L-conjugacy orbit of k whose differences lie in Z injects into Z. Thus
its centralizer has index at most |Z|, and the same bound holds for its
surjective quotient image. If that image contains the required parabolic,
each parabolic element differs from a centralizing lift by a kernel element.
Kernel normalization then preserves K. Two-perfect commutator idempotence
supplies centralization once the small intersection K ∩ Z is centralized.

These are finite-group ingredients for the normalization step of MS93,
*Pushing up weak BN-pairs of rank two* (1993), printed p.883, before (1.7)(i).
The quotient-overgroup hypothesis here is discharged in SmallInvariant.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Lifting
open Subgroup
open scoped commutatorElement

private theorem centralizer_index_le_card_of_commutator
    {G : Type*} [Group G] [Finite G] (L Z : Subgroup G) (k : G)
    (hcomm : ∀ l ∈ L, ⁅l, k⁆ ∈ Z) :
    ((centralizer ({k} : Set G)).subgroupOf L).index ≤ Nat.card Z := by
  let : MulAction L G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp L.subtype)
  have hstab : MulAction.stabilizer L k = (centralizer ({k} : Set G)).subgroupOf L := by
    ext g
    change (g : G) * k * (g : G)⁻¹ = k ↔ _
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.symm
  have hm (x : MulAction.orbit L k) : (x : G) * k⁻¹ ∈ Z := by
    obtain ⟨l, hl⟩ := x.property
    rw [← hl]
    exact hcomm l l.property
  let f : MulAction.orbit L k → Z := fun x => ⟨(x : G) * k⁻¹, hm x⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact mul_right_cancel (congrArg Subtype.val h)
  rw [← hstab, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

private theorem normalized_of_centralizer_images
    {G H : Type*} [Group G] [Group H] (π : G →* H)
    (P K L : Subgroup G)
    (hQ : π.ker ≤ normalizer (K : Set G))
    (himage : ∀ k ∈ K, P.map π ≤ (L ⊓ centralizer ({k} : Set G)).map π) :
    P ≤ normalizer (K : Set G) := by
  apply le_normalizer_iff.mpr
  intro p hp k hk
  obtain ⟨c, hc, he⟩ := himage k hk (mem_map_of_mem π hp)
  have hq : p * c⁻¹ ∈ π.ker := by
    change π (p * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hck : c * k = k * c := mem_centralizer_singleton_iff.mp hc.2
  have hh := (mem_normalizer_iff.mp (hQ hq) k).mp hk
  have hci : c⁻¹ * k * c = k := by
    rw [mul_assoc, ← hck, inv_mul_cancel_left]
  have heq : (p * c⁻¹) * k * (p * c⁻¹)⁻¹ = p * (c⁻¹ * k * c) * p⁻¹ := by group
  rwa [heq, hci] at hh

/-- Centralizer images containing a prescribed quotient subgroup lift its action
through a kernel already normalizing K. The index bound comes from [K,L] ≤ Z. -/
theorem normalized_of_small_centralizer_overgroups
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (π : G →* H) (P K L Z T : Subgroup G) (d : ℕ)
    (hL : L.map π = ⊤) (hTL : T ≤ L)
    (hQ : π.ker ≤ normalizer (K : Set G))
    (hcomm : ⁅K,L⁆ ≤ Z) (hcard : Nat.card Z ≤ d)
    (hTK : T ≤ centralizer (K : Set G))
    (hmodel : ∀ A : Subgroup H, T.map π ≤ A → A.index ≤ d → P.map π ≤ A) :
    P ≤ normalizer (K : Set G) := by
  apply normalized_of_centralizer_images π P K L hQ
  intro k hk
  let C := (centralizer ({k} : Set G)).subgroupOf L
  have hπL : Function.Surjective (π.comp L.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rwa [MonoidHom.range_comp, range_subtype]
  have hC : C.map (π.comp L.subtype) = (L ⊓ centralizer ({k} : Set G)).map π := by
    rw [← map_map]
    congr 1
    ext x
    exact ⟨fun ⟨l, hl, he⟩ => he ▸ ⟨l.property, hl⟩,
      fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩⟩
  have hind : ((L ⊓ centralizer ({k} : Set G)).map π).index ≤ d := by
    rw [← hC]
    apply (Nat.le_of_dvd (Nat.card_pos (α := L ⧸ C)) (C.index_map_dvd hπL)).trans
    apply (centralizer_index_le_card_of_commutator L Z k ?_).trans hcard
    intro l hl
    apply hcomm
    rw [commutator_comm]
    exact commutator_mem_commutator hl hk
  apply hmodel _ ?_ hind
  apply map_mono
  intro t ht
  refine ⟨hTL ht, mem_centralizer_singleton_iff.mpr ?_⟩
  exact (hTK ht k hk).symm


/-- A two-perfect residual centralizes a two-subgroup if its commutator lies
in a central intersection. No ambient normality of K is required. -/
theorem centralizes_of_intersection_centralizes {G : Type*} [Group G] [Finite G]
    (P K Z : Subgroup G) (hK : IsPGroup 2 K)
    (hn : (pResidual 2 P).map P.subtype ≤ normalizer (K : Set G))
    (hc : ⁅K, pResidual 2 G⁆ ≤ Z)
    (hJ : K ⊓ Z ≤ centralizer (P : Set G)) :
    (pResidual 2 P).map P.subtype ≤ centralizer (K : Set G) := by
  let T := (pResidual 2 P).map P.subtype
  have hTL : T ≤ pResidual 2 G := map_pResidual_le 2 P.subtype
  have hcomm : ⁅K,T⁆ ≤ K ⊓ Z :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      ((commutator_mono le_rfl hTL).trans hc)
  have hfix : ⁅K ⊓ Z,T⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hJ.trans (centralizer_le (map_subtype_le _)))
  have hh : ⁅K,T⁆ = ⊥ := by
    rw [← commutator_isPPerfect_idempotent T K
      (isPPerfect_embedded_pResidual 2 P) hK hn]
    exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans hfix.le)
  rw [commutator_comm] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp hh


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Lifting
