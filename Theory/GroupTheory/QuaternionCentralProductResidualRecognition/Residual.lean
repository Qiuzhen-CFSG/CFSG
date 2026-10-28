module

public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Transport and generators of the p-residual

Homomorphisms map the p-residual into the target residual: pull back every
normal subgroup with p-group quotient through the composite quotient map.
Isomorphisms therefore preserve residuals, and the residual is characteristic.
Elements of order coprime to p vanish in every p-group quotient.

These facts support the strict-enlargement step of Aschbacher–Smith,
Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace Subgroup

/-- Every homomorphism maps the p-residual into the target residual. -/
public theorem map_pResidual_le {G K : Type*} [Group G] [Group K] (p : ℕ) (f : G →* K) :
    (pResidual p G).map f ≤ pResidual p K := by
  apply le_sInf
  rintro N ⟨hN, hp⟩
  let := hN
  let q := (QuotientGroup.mk' N).comp f
  have hr : IsPGroup p q.range := hp.of_injective q.range.subtype q.range.subtype_injective
  have hk : IsPGroup p (G ⧸ q.ker) :=
    hr.of_equiv (QuotientGroup.quotientKerEquivRange q).symm
  rintro x ⟨y, hy, rfl⟩
  have hy' : y ∈ q.ker := (sInf_le ⟨inferInstance, hk⟩ : pResidual p G ≤ q.ker) hy
  exact (QuotientGroup.eq_one_iff (f y)).mp (MonoidHom.mem_ker.mp hy')

/-- Isomorphisms preserve the p-residual. -/
public theorem map_pResidual {G K : Type*} [Group G] [Group K] (p : ℕ) (e : G ≃* K) :
    (pResidual p G).map e.toMonoidHom = pResidual p K := by
  apply le_antisymm (map_pResidual_le p e.toMonoidHom)
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_pResidual_le p e.symm.toMonoidHom)
  simpa [Subgroup.map_map] using h

public instance pResidual_characteristic {G : Type*} [Group G] (p : ℕ) :
    (pResidual p G).Characteristic := by
  apply characteristic_iff_map_le.mpr
  intro e
  exact map_pResidual_le p e.toMonoidHom

public instance pResidual_normal {G : Type*} [Group G] (p : ℕ) :
    (pResidual p G).Normal := inferInstance

/-- Strict enlargement of the embedded residual forces a proper subgroup. -/
public theorem ne_top_of_map_pResidual_lt {G : Type*} [Group G] (p : ℕ) (H : Subgroup G)
    (h : (pResidual p H).map H.subtype < pResidual p G) : H ≠ ⊤ := by
  intro heq
  subst H
  have he := map_pResidual p (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  exact (ne_of_lt h) he

/-- Elements of order coprime to p belong to the p-residual. -/
public theorem mem_pResidual_of_orderOf_coprime {G : Type*} [Group G] {p : ℕ} {x : G}
    (hx : Nat.Coprime p (orderOf x)) : x ∈ pResidual p G := by
  rw [pResidual, mem_sInf]
  rintro N ⟨hN, hp⟩
  let := hN
  apply (QuotientGroup.eq_one_iff x).mp
  obtain ⟨n, hn⟩ := hp.exists_orderOf_dvd_pow (QuotientGroup.mk' N x)
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hx.pow_left n) hn
    (orderOf_map_dvd (QuotientGroup.mk' N) x)


end Subgroup
