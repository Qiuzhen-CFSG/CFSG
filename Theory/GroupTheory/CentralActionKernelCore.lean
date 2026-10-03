module
public import Theory.GroupTheory.OddActionCentralTwoKernel
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupAction.SubgroupConjugation

/-!
# Identifying a normal kernel from central two-layers

Let Q be a normal two-subgroup of a finite group P which contains its
centralizer. Suppose a normal subgroup K contains Q, meets a Sylow
two-subgroup in Q, and acts trivially on Z and Q/Z, where Z is central
in Q. Then K equals Q.

The Sylow intersection makes K/Q odd. Schur–Zassenhaus supplies an odd
complement in K. Its action on Q is trivial by the central two-kernel
discrepancy theorem: it fixes both the central kernel Z and the quotient.
The self-centralization of Q forces the complement into Q, so generation
by Q and that complement identifies K with Q.

This is the ordinary action-kernel transfer needed after identifying the
chief preimage in Stellmacher (9.1), Journal of Algebra190 (1997), p.48.
The lemma is independent of that configuration.
-/
namespace Subgroup
open scoped commutatorElement
public theorem eq_of_sylow_intersection_of_central_action_layers
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (Q K Z : Subgroup P) [Q.Normal] [K.Normal]
    (hQ : IsPGroup 2 Q) (hQK : Q ≤ K)
    (hKS : K ⊓ (S : Subgroup P) = Q)
    (hZQ : Z ≤ Q) (hZcentral : Z ≤ centralizer (Q : Set P))
    (hKZ : K ≤ centralizer (Z : Set P)) (hQKcomm : ⁅Q,K⁆ ≤ Z)
    (hself : centralizer (Q : Set P) ≤ Q) : K = Q := by
  let QK := Q.subgroupOf K
  have hQKp : IsPGroup 2 QK := hQ.comap_subtype
  obtain ⟨inner, hinner⟩ := S.exists_subgroupOf_eq_of_normal K
  have hsub : (S : Subgroup P).subgroupOf K = QK := by
    ext x
    constructor
    · intro hx
      exact hKS.le ⟨x.property, hx⟩
    · intro hx
      exact (hKS.ge hx).2
  have hodd : Odd QK.index := by
    rw [← hsub, ← hinner, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact inner.not_dvd_index
  have hcop : Nat.Coprime (Nat.card QK) QK.index := by
    obtain ⟨n, hn⟩ := hQKp.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  obtain ⟨R0,hR0⟩ := exists_right_complement'_of_coprime hcop
  let R := R0.map K.subtype
  have hRK : R ≤ K := map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [card_map_of_injective K.subtype_injective, ← hR0.symm.index_eq_card]
    exact hodd
  have hcover : Q ⊔ R = K := by
    have hh := congrArg (Subgroup.map K.subtype) hR0.sup_eq_top
    rw [map_sup, map_subgroupOf_eq_of_le hQK, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  let _ : MulDistribMulAction R Q := conjMulDistribMulActionOfLeNormalizer R Q le_normalizer_of_normal
  have hZcenter : Z.subgroupOf Q ≤ center Q := by
    intro z hz
    rw [mem_center_iff]
    intro q
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hZcentral hz) q q.property
  have hZtwo : IsPGroup 2 (Z.subgroupOf Q) := (hQ.to_le hZQ).comap_subtype
  have hfix : ∀ r : R, ∀ z ∈ Z.subgroupOf Q, r • z = z := by
    intro r z hz
    apply Subtype.ext
    change (r : P) * (z : P) * (r : P)⁻¹ = z
    have hh := mem_centralizer_iff.mp (hKZ (hRK r.property)) z hz
    rw [← hh, mul_inv_cancel_right]
  have hquot : ∀ r : R, ∀ q : Q, (r • q) * q⁻¹ ∈ Z.subgroupOf Q := by
    intro r q
    change (r : P) * (q : P) * (r : P)⁻¹ * (q : P)⁻¹ ∈ Z
    have hh : ⁅(r : P), (q : P)⁆ ∈ ⁅Q,K⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator (hRK r.property) q.property
    exact hQKcomm hh
  have htrivial := MulDistribMulAction.trivial_of_odd_of_central_two_kernel
    hRodd (Z.subgroupOf Q) hZcenter hZtwo hfix hquot
  have hRQ : R ≤ Q := by
    apply le_trans _ hself
    intro r hr
    rw [mem_centralizer_iff]
    intro q hq
    have hh := congrArg Subtype.val (htrivial ⟨r,hr⟩ ⟨q,hq⟩)
    change r * q * r⁻¹ = q at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [← hcover, sup_eq_left.mpr hRQ]
end Subgroup
