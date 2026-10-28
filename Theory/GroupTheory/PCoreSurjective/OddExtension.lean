module

public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Rank

/-!
# Odd extensions and transport modulo the two-core

A surjection with two-group kernel induces an isomorphism after removing
both intrinsic two-cores. If the target has a nontrivial normal p-subgroup
with two-group quotient, p odd, that subgroup maps to the full p-core of
the two-core quotient. Full commutation with a rank-one subgroup survives,
and forces the latter subgroup's image still to have rank one.

These elementary extension calculations verify the intrinsic E1 conditions
for lifts of proper subgroups in Aschbacher–Smith, E.5.2, printed p.243
(combined manuscript, 1 March 2004).
-/

open Subgroup

namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- Removing the p-cores identifies a group and any quotient with p-group kernel. -/
public noncomputable def quotientPCoreEquivOfSurjective {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    (G ⧸ pCore p G) ≃* (H ⧸ pCore p H) := by
  let g := (QuotientGroup.mk' (pCore p H)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = pCore p G := by
    rw [show g.ker = (pCore p H).comap f from by
      ext x
      exact QuotientGroup.eq_one_iff (f x)]
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)

/-- The core quotient equivalence commutes with the given surjection. -/
public theorem quotientPCoreEquivOfSurjective_mk {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) (x : G) :
    quotientPCoreEquivOfSurjective f hf hk (QuotientGroup.mk' (pCore p G) x) =
      QuotientGroup.mk' (pCore p H) (f x) := by
  rfl

end MonoidHom

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A normal odd-prime subgroup with two-group quotient is the full prime core. -/
public theorem odd_core_of_normal_p_subgroup {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) (hq : IsPGroup 2 (G ⧸ N)) :
    pCore p G = N := by
  have hNcore : N ≤ pCore p G := le_sSup ⟨inferInstance, hN⟩
  apply le_antisymm ?_ hNcore
  let q := QuotientGroup.mk' N
  have hz : (pCore p G).map q = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne p 2 hp _ _ (pCore_isPGroup.map q)
      (hq.to_subgroup _))
  simpa only [q, map_eq_bot_iff, QuotientGroup.ker_mk'] using hz

omit [Finite G] in
/-- Its image is still the full odd core after taking the intrinsic two-core quotient. -/
public theorem odd_core_mod_twoCore {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) (hq : IsPGroup 2 (G ⧸ N)) :
    let q := QuotientGroup.mk' (pCore 2 G)
    pCore p (G ⧸ pCore 2 G) = N.map q ∧
      IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ N.map q) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let _ : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let g := (QuotientGroup.mk' (N.map q)).comp q
  have hNg : N ≤ g.ker := by
    intro n hn
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem q hn)
  let f := QuotientGroup.lift N g hNg
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := ((QuotientGroup.mk'_surjective _).comp
      (QuotientGroup.mk'_surjective _)) x
    exact ⟨QuotientGroup.mk' N y, hy⟩
  have htwo := hq.of_surjective f hf
  exact ⟨odd_core_of_normal_p_subgroup hp _ (hN.map q) htwo, htwo⟩

/-- The odd core, full commutation, and rank one survive removal of the two-core. -/
public theorem odd_quotient_commutator_rank {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (N B : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hq : IsPGroup 2 (G ⧸ N)) (hne : N ≠ ⊥)
    (hcomm : N = ⁅N, B⁆) (hrank : Group.rank B = 1) :
    let Q := G ⧸ pCore 2 G
    let b := B.map (QuotientGroup.mk' (pCore 2 G))
    IsPGroup 2 (Q ⧸ pCore p Q) ∧ pCore p Q ≠ ⊥ ∧
      pCore p Q = ⁅pCore p Q, b⁆ ∧ Group.rank b = 1 := by
  have hstructure := odd_core_mod_twoCore hp N hN hq
  let q := QuotientGroup.mk' (pCore 2 G)
  have hne' : N.map q ≠ ⊥ := by
    intro hz
    have hle : N ≤ pCore 2 G := by
      simpa only [q, map_eq_bot_iff, QuotientGroup.ker_mk'] using hz
    exact hne (disjoint_iff.mp
      (IsPGroup.disjoint_of_ne p 2 hp N (pCore 2 G) hN pCore_isPGroup) ▸
        (inf_eq_left.mpr hle).symm)
  have hc : N.map q = ⁅N.map q, B.map q⁆ := by
    conv_lhs => rw [hcomm]
    rw [map_commutator]
  have hbne : B.map q ≠ ⊥ := by
    intro hb
    apply hne'
    simpa only [hb, commutator_bot_right] using hc
  let : Nontrivial (B.map q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbne
  have hrle : Group.rank (B.map q) ≤ 1 := by
    rw [← hrank]
    exact Group.rank_le_of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hstructure.2.of_equiv (QuotientGroup.quotientMulEquivOfEq hstructure.1.symm)
  · rwa [hstructure.1]
  · rwa [hstructure.1]
  · exact Nat.le_antisymm hrle (Nat.succ_le_of_lt (Group.rank_pos (G := B.map q)))
end Subgroup

namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- The same conclusions lift through any surjection with two-group kernel. -/
public theorem odd_quotient_commutator_rank_of_surjective {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (N : Subgroup H) [N.Normal] (B : Subgroup G) (hN : IsPGroup p N)
    (hq : IsPGroup 2 (H ⧸ N)) (hne : N ≠ ⊥)
    (hcomm : N = ⁅N, B.map f⁆) (hrank : Group.rank (B.map f) = 1) :
    let Q := G ⧸ pCore 2 G
    let b := B.map (QuotientGroup.mk' (pCore 2 G))
    IsPGroup 2 (Q ⧸ pCore p Q) ∧ pCore p Q ≠ ⊥ ∧
      pCore p Q = ⁅pCore p Q, b⁆ ∧ Group.rank b = 1 := by
  obtain ⟨hquot, hnon, hcom, hr⟩ := odd_quotient_commutator_rank hp N (B.map f)
    hN hq hne hcomm hrank
  let e := MonoidHom.quotientPCoreEquivOfSurjective f hf hk
  let b := B.map (QuotientGroup.mk' (pCore 2 G))
  have hb : b.map e.toMonoidHom = (B.map f).map (QuotientGroup.mk' (pCore 2 H)) := by
    rw [map_map, map_map]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hquot.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso p e)).symm
  · intro hz
    apply hnon
    rw [← pCore_map_iso p e, hz, map_bot]
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator, pCore_map_iso, hb]
    exact hcom
  · exact (Group.rank_congr ((b.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hb))).trans hr
end Subgroup
