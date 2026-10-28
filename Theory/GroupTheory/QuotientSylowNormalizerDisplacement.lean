module
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Lifting quotient displacements to a Sylow normalizer

When the kernel lies in the Sylow intersection, membership in the quotient
Sylow image lifts back to that same intersection. Thus a local element
whose displacements under every Sylow actor lie in this image normalizes
the original Sylow subgroup, including the actors outside the local factor.

Source application: Aschbacher--Smith 11.5.6(3), printed p.781, the
subfield Borel acting on the original Sylow two-subgroup.
-/

public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- Quotient displacements in the Sylow intersection force normalization of
that same Sylow subgroup, including its elements outside the local factor. -/
theorem mem_normalizer_of_quotient_displacements
    (T I : Subgroup G) (hn : T ≤ normalizer (I : Set G))
    (q : I →* Q) (hk : q.ker ≤ T.subgroupOf I)
    (a : T → MulAut Q)
    (ha : ∀ (t : T) (i : I), a t (q i) = q (I.normalizerMonoidHom ⟨t,hn t.property⟩ i))
    (b : I)
    (hb : ∀ t : T, (q b)⁻¹ * a t (q b) ∈ (T.subgroupOf I).map q) :
    (b : G) ∈ normalizer (T : Set G) := by
  rw [← inv_mem_iff]
  apply mem_normalizer_fintype
  intro t ht
  let t' : T := ⟨t,ht⟩
  let d : I := b⁻¹ * I.normalizerMonoidHom ⟨t,hn ht⟩ b
  have hd : d ∈ T.subgroupOf I := by
    have hh : d ∈ ((T.subgroupOf I).map q).comap q := by
      change q d ∈ (T.subgroupOf I).map q
      rw [map_mul,map_inv,← ha t' b]
      exact hb t'
    rwa [comap_map_eq_self hk] at hh
  have hh := T.mul_mem hd ht
  change (b : G)⁻¹ * (t * (b : G) * t⁻¹) * t ∈ T at hh
  change (b : G)⁻¹ * t * ((b : G)⁻¹)⁻¹ ∈ T
  simpa only [d, Subgroup.coe_mul, Subgroup.coe_inv,
    normalizerMonoidHom_apply_apply_coe, mul_assoc, inv_mul_cancel, mul_one, inv_inv]
    using hh
end Subgroup
