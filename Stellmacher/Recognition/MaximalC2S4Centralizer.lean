module

public import Theory.Quasithin
public import Theory.PGroupCore
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!

# Full involution centralizers in the maximal C₂ times S₄ branch

A maximal two-local subgroup isomorphic to `C₂ × S₄` is the full centralizer
of an involution of the ambient group. Transport the nonidentity element of
the central `C₂` factor into the subgroup. Its centralizer contains that
subgroup and lies in the normalizer of its cyclic group of order two.
Maximal two-locality forces this normalizer, and hence the centralizer, to
equal the original subgroup. Neither simplicity nor the N₂ condition is
needed.

The companion normalizer statement holds for every maximal two-local
subgroup. Its defining local witness lies in the internal two-core, making
that core nontrivial. Normality places the subgroup in the ambient core
normalizer, and maximality again forces equality.

This is the full-centralizer input for alternative (c) of Stellmacher's
Theorem 2, following the centralizer observation in Kurzweil–Stellmacher,
The Theory of Finite Groups, Chapter 12, printed p. 367. It extracts that
observation without the source chapter's additional Z condition.
-/

namespace Stellmacher.Recognition

private theorem central_involution_of_c2s4
    {K : Type*} [Group K]
    (e : K ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    ∃ t : K, orderOf t = 2 ∧ t ∈ Subgroup.center K := by
  let c : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) :=
    (Multiplicative.ofAdd 1, 1)
  have hc2 : c ^ 2 = 1 := by
    apply Prod.ext
    · decide
    · simp [c]
  have hcne : c ≠ 1 := by
    intro h
    have hfirst := congrArg Prod.fst h
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1) hfirst
  have hccomm (x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) : x * c = c * x := by
    apply Prod.ext
    · exact mul_comm _ _
    · simp [c]
  refine ⟨e.symm c, (e.symm.orderOf_eq c).trans (orderOf_eq_prime hc2 hcne), ?_⟩
  rw [Subgroup.mem_center_iff]
  intro x
  apply e.injective
  simpa only [map_mul, MulEquiv.apply_symm_apply] using hccomm (e x)

/-- A maximal two-local `C₂ × S₄` subgroup is the full centralizer of an
ambient involution. -/
public theorem exists_involution_centralizer_of_maximal_c2s4
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (hP : IsMaximalTwoLocal P)
    (hModel : Nonempty (P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    ∃ t : G, orderOf t = 2 ∧ Subgroup.centralizer ({t} : Set G) = P := by
  obtain ⟨e⟩ := hModel
  obtain ⟨t, ht, htcenter⟩ := central_involution_of_c2s4 e
  have htG : orderOf (t : G) = 2 := by
    simpa only [Subgroup.orderOf_coe] using ht
  have hPC : P ≤ Subgroup.centralizer ({(t : G)} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun y : P => (y : G))
      (Subgroup.mem_center_iff.mp htcenter ⟨x, hx⟩)
  have hQne : Subgroup.zpowers (t : G) ≠ ⊥ := by
    intro hbot
    have hone := Subgroup.zpowers_eq_bot.mp hbot
    simp [hone] at htG
  have hQp : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
    IsPGroup.of_card (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using htG)
  have hCN : Subgroup.centralizer ({(t : G)} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hNP : Subgroup.normalizer (Subgroup.zpowers (t : G) : Set G) ≤ P :=
    hP.2 ⟨Subgroup.zpowers (t : G), hQne, hQp, rfl⟩ (hPC.trans hCN)
  exact ⟨t, htG, le_antisymm (hCN.trans hNP) hPC⟩

/-- Every maximal two-local subgroup is the normalizer of its ambient
two-core. -/
public theorem normalizer_twoCore_eq_of_maximal_twoLocal
    {G : Type*} [Group G] (P : Subgroup G) (hP : IsMaximalTwoLocal P) :
    Subgroup.normalizer ((pCore 2 P).map P.subtype : Set G) = P := by
  obtain ⟨Q, hQne, hQp, hPQ⟩ := hP.1
  have hQP : Q ≤ P := by
    rw [hPQ]
    exact Subgroup.le_normalizer
  have hQnormal : (Q.subgroupOf P).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (by rw [hPQ])
  have hQcore : Q ≤ (pCore 2 P).map P.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQP]
    exact Subgroup.map_mono (show Q.subgroupOf P ≤ pCore 2 P from
      le_sSup ⟨hQnormal, hQp.comap_subtype⟩)
  have hcoreNe : (pCore 2 P).map P.subtype ≠ ⊥ := by
    intro hbot
    exact hQne (le_bot_iff.mp (hbot ▸ hQcore))
  have hPN : P ≤ Subgroup.normalizer ((pCore 2 P).map P.subtype : Set G) := by
    have h := (pCore 2 P).le_normalizer_map P.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact le_antisymm
    (hP.2 ⟨(pCore 2 P).map P.subtype, hcoreNe, pCore_isPGroup.map P.subtype, rfl⟩ hPN)
    hPN

end Stellmacher.Recognition
