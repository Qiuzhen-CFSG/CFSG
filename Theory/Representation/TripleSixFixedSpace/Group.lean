module

public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NormNum

/-!
# Small group facts for a triple cover of A₆

A subgroup of order forty in A₆ would contain a five-cycle. Its five moved
points form a full subgroup orbit, so the subgroup fixes the remaining point
and would lie in A₅, contradicting Lagrange's theorem. The same obstruction
holds in any extension of A₆ by a group of order three, because a subgroup
of order forty embeds in the quotient. Such an extension has order 1080
and contains an element of order four.

These elementary facts supply the intrinsic orbit calculation for the
three-dimensional F₄ action in Aschbacher–Smith, K.1.3, printed p.453,
and the exclusion used in 15.4.18, printed p.1163.
-/

public section
namespace Representation.TripleSixFixedSpace
open Subgroup MulAction

/-- The alternating group on six letters has no subgroup of order forty. -/
theorem six_no_forty (H : Subgroup (alternatingGroup (Fin 6))) : Nat.card H ≠ 40 := by
  classical
  intro hH
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 (by rw [hH]; decide)
  let σ : Equiv.Perm (Fin 6) := a.val.val
  have ho : orderOf σ = 5 := by
    simpa only [σ, Subgroup.orderOf_coe] using ha
  have hc : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (ho ▸ (by decide : Nat.Prime 5)) (by simp [ho])
  have hs : σ.support.card = 5 := hc.orderOf.symm.trans ho
  obtain ⟨x, hx⟩ := hc.nonempty_support
  let O : Set (Fin 6) := orbit H x
  have hsub : (σ.support : Set (Fin 6)) ⊆ O := by
    intro y hy
    obtain ⟨n, hn⟩ := hc.exists_pow_eq
      (Equiv.Perm.mem_support.mp hx) (Equiv.Perm.mem_support.mp hy)
    exact ⟨a ^ n, hn⟩
  have hlo : 5 ≤ O.ncard := by
    simpa only [Set.ncard_coe_finset, hs] using Set.ncard_le_ncard hsub
  have hhi : O.ncard ≤ 6 := by simpa using O.ncard_le_card
  have hdvd : O.ncard ∣ 40 := by
    rw [← hH, ← MulAction.index_stabilizer H x]
    exact (stabilizer H x).index_dvd_card
  have hO : O.ncard = 5 := by
    have hn : O.ncard ≠ 6 := by
      intro he
      norm_num [he] at hdvd
    omega
  have hC : Oᶜ.ncard = 1 := by
    rw [Set.ncard_compl, hO]
    simp
  obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hC
  have hyO : y ∉ O := by rw [← Set.mem_compl_iff, hy]; simp
  have hfix (g : H) : g • y = y := by
    have hnot : g • y ∉ O := by
      rintro ⟨k, hk⟩
      apply hyO
      refine ⟨g⁻¹ * k, ?_⟩
      change (g⁻¹ * k) • x = y
      change k • x = g • y at hk
      rw [mul_smul, hk, inv_smul_smul]
    have hmem : g • y ∈ Oᶜ := hnot
    simpa only [hy, Set.mem_singleton_iff] using hmem
  let K := fixingSubgroup (alternatingGroup (Fin 6)) ({y} : Set (Fin 6))
  have hle : H ≤ K := by
    intro g hg z
    have hz : z.val = y := z.property
    change g.val z.val = z.val
    rw [hz]
    exact hfix ⟨g, hg⟩
  have hK : Nat.card K = 60 := by
    let : Nontrivial ↥(({y} : Finset (Fin 6))ᶜ) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by simp)
    dsimp only [K]
    rw [← Finset.coe_singleton]
    rw [Nat.card_congr
      (Atlas.Families.Alternating.stabilizerComplementEquiv ({y} : Finset (Fin 6))).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Fintype.card_compl_set, Nat.factorial]
  have hh := card_dvd_of_le hle
  rw [hH, hK] at hh
  norm_num at hh

variable {G : Type*} [Group G] [Finite G]
  (q : G →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
  (hk : Nat.card q.ker = 3)

omit [Finite G] in
include q hq hk in
/-- The extension order uses the actual quotient map and its kernel. -/
theorem cover_card : Nat.card G = 1080 := by
  have hr : Nat.card q.range = 360 := by
    rw [MonoidHom.range_eq_top.mpr hq, Nat.card_congr (Subgroup.topEquiv).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have h := q.ker.card_mul_index
  rw [Subgroup.index_ker, hk, hr] at h
  exact h.symm

omit [Finite G] in
include q hk in
/-- An order-forty subgroup embeds across the odd kernel and is impossible. -/
theorem cover_no_forty (K : Subgroup G) : Nat.card K ≠ 40 := by
  intro hK
  let f := q.comp K.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    have hxq : x.val ∈ q.ker := hx
    have h₁ : orderOf x ∣ 40 := hK ▸ orderOf_dvd_natCard x
    have h₂ : orderOf x ∣ 3 := by
      have hh := orderOf_dvd_natCard (⟨x.val, hxq⟩ : q.ker)
      rw [← Subgroup.orderOf_coe] at hh
      change orderOf x.val ∣ Nat.card q.ker at hh
      simpa only [Subgroup.orderOf_coe, hk] using hh
    have h₃ : orderOf x ∣ 1 := Nat.dvd_gcd h₁ h₂
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one h₃)
  have hr : Nat.card f.range = 40 :=
    (Nat.card_congr (Equiv.ofInjective f hf)).symm.trans hK
  exact six_no_forty f.range hr

private def fourCycle : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    change Equiv.Perm.sign _ = 1
    decide⟩

private theorem fourCycle_order : orderOf fourCycle = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

include q hq in
/-- A lift of a four-cycle has a power of order exactly four. -/
theorem cover_has_four : ∃ x : G, orderOf x = 4 := by
  obtain ⟨g, hg⟩ := hq fourCycle
  have hd : 4 ∣ orderOf g := by
    rw [← fourCycle_order, ← hg]
    exact orderOf_map_dvd q g
  exact ⟨g ^ (orderOf g / 4), orderOf_pow_orderOf_div (orderOf_pos g).ne' hd⟩

end Representation.TripleSixFixedSpace
