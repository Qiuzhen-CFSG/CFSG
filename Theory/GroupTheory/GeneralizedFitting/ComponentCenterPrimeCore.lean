module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.PPrimeCore

/-!
# Centers of components when the prime-complement core is trivial

Triviality of O_{p'} descends along a subnormal chain: at each normal step
its characteristic core maps into the core of the larger group. For a
quasisimple group with trivial O_{p'}, the center is a normal nilpotent
p-group and equals O_p, since the p-core of a quasisimple group is central.

This is the catalogue-independent part of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.2(1), p.1170.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem core_bot_of_normal {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (h : pPrimeCore p G = ⊥)
    (N : Subgroup G) [N.Normal] : pPrimeCore p N = ⊥ := by
  apply (map_eq_bot_iff_of_injective _ N.subtype_injective).mp
  apply le_bot_iff.mp
  simpa only [h] using pPrimeCore_map_subtype_le_pPrimeCore_of_normal p N

/-- Trivial prime-complement core passes to subnormal subgroups. -/
public theorem Subgroup.IsSubnormal.pPrimeCore_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (h : pPrimeCore p G = ⊥)
    (N : Subgroup G) (hN : N.IsSubnormal) : pPrimeCore p N = ⊥ := by
  induction hN with
  | top =>
    have hh := pPrimeCore_map_iso p (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    rw [h] at hh
    exact (map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).mp hh
  | step N K hNK _ hn ih =>
    let := hn
    have hb := core_bot_of_normal ih (N.subgroupOf K)
    have hh := pPrimeCore_map_iso p (subgroupOfEquivOfLe hNK)
    simpa only [hb, Subgroup.map_bot] using hh.symm

/-- A quasisimple group with trivial prime-complement core has p-group center,
equal to its p-core. -/
public theorem Theory.GroupTheory.IsQuasisimple.center_eq_pCore {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    {p : ℕ} [Fact p.Prime] (h : pPrimeCore p G = ⊥) :
    center G = pCore p G := by
  have hp : IsPGroup p (center G) :=
    isPGroup_of_nilpotent_normal (p := p) (center G) inferInstance inferInstance h
  exact le_antisymm (le_sSup ⟨inferInstance, hp⟩) (IsQuasisimple.pCore_le_center p)
