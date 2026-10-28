module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.Fibers.Pairs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.Shearing

/-!
# The actor fiber as odd-product pairs in its distinguished centralizer

The ordered Thompson fiber `(s,b)` at an involution `u` corresponds to
`(u*b,s)` in `Lᵤ = centralizerClosure Z u`, with inverse `(a,b) ↦ (b,u*a)`.
The dihedral half-order identities and the exclusion `u ∉ Lᵤ` prove the
forward direction. Shearing proves the reverse direction. Equal factors
are retained: their product has order one.

This extends the collapsed-linear correspondence without assuming collapse,
any model count, or that the initially chosen distinguished `z` commutes
with `u`. The last theorem applies the correspondence to the original proper
residual inputs, leaving only the local odd-pair cardinality to be counted.
Source: GLS4, Chapter 2, proof of Lemma 12.8, `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
namespace ResidualFiberCorrespondence

omit [Finite G] in
private theorem involution_pow_odd {u : G} (hu : u ^ 2 = 1) {k : ℕ} (hk : Odd k) :
    u ^ k = u := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_add, pow_mul, hu]
  simp

omit [Finite G] in
private theorem half_power_mul_odd {u x : G} (hu : PFAppendixIII.IsInvolution u)
    (hc : Commute u x) (ho : Odd (orderOf x)) :
    (u * x) ^ (orderOf (u * x) / 2) = u := by
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have he : orderOf (u * x) = 2 * orderOf x := by
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (hu2 ▸ ho.coprime_two_left), hu2]
  rw [he, Nat.mul_div_right _ (by decide : 0 < 2), hc.mul_pow,
    pow_orderOf_eq_one, mul_one, involution_pow_odd hu.sq_eq_one ho]

omit [Finite G] in
private theorem mem_Z_of_isConj (h : IsProductDisconnected Z M)
    {a b : G} (ha : a ∈ Z) (hab : IsConj a b) : b ∈ Z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  exact hg ▸ h.invariant g a ha

private theorem isConj_of_local_involution
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (x : centralizerClosure Z u) (hx : orderOf x = 2) : IsConj z (x : G) := by
  have hxI : PFAppendixIII.IsInvolution (x : G) := by
    apply (orderOf_eq_prime_iff.mp ?_).symm
    exact (orderOf_coe x).trans hx
  exact r.one_class z hz x
    ((pair_involution_centralizerClosure_involutions h r htM huD hu x.property).mp hxI)

private theorem fiber_local_pair
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (p : Fiber z u u) :
    u * p.val.2 ∈ centralizerClosure Z u ∧ p.val.1 ∈ centralizerClosure Z u ∧
      orderOf (u * p.val.2) = 2 ∧ orderOf p.val.1 = 2 ∧
        Odd (orderOf ((u * p.val.2) * p.val.1)) := by
  let s := p.val.1
  let v := p.val.2
  have hsZ : s ∈ Z := mem_Z_of_isConj h hz p.property.1
  have hsI := h.involutions s hsZ
  have hs2 : orderOf s = 2 := orderOf_eq_prime hsI.sq_eq_one hsI.ne_one
  have hz2 : orderOf z = 2 := orderOf_eq_prime (h.involutions z hz).sq_eq_one (h.involutions z hz).ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have hvI : PFAppendixIII.IsInvolution v := by
    obtain ⟨g, hg⟩ := isConj_iff.mp p.property.2.1
    change PFAppendixIII.IsInvolution p.val.2
    rw [← hg]
    exact BenderSuzuki.IsInvolution.map_of_injective hu
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hv2 : orderOf v = 2 := orderOf_eq_prime hvI.sq_eq_one hvI.ne_one
  have huZ : u ∉ Z := not_mem_Z_of_mem_residualPairStabilizer h htM
    huD
  have hnot : ¬ IsConj z u := fun he => huZ (mem_Z_of_isConj h hz he)
  have hw := halfOrder_properties hz2 hu2 hnot p.property.1 p.property.2.1
  rw [p.property.2.2] at hw
  change orderOf u = 2 ∧ Commute u s ∧ Commute u v at hw
  have hsL : s ∈ centralizerClosure Z u :=
    mem_centralizerClosure hsZ hw.2.1.symm
  have hhalf : halfOrder s v = u := p.property.2.2
  have heven : Even (orderOf (s * v)) := by
    apply Nat.not_odd_iff_even.mp
    intro ho
    have he := isConj_of_involutions_odd_product s v hsI.sq_eq_one hvI.sq_eq_one ho
    exact hnot (p.property.1.trans (he.trans p.property.2.1.symm))
  have hmod : orderOf (s * v) % 4 = 2 := by
    by_contra hn
    have hd : orderOf (s * v) % 4 = 0 := by obtain ⟨k, hk⟩ := heven; omega
    have hsuZ := mem_Z_of_isConj h hsZ (DihedralHalfOrderClasses.preserve hs2 hv2 hd).1
    rw [hhalf] at hsuZ
    have hsuL : s * u ∈ centralizerClosure Z u :=
      mem_centralizerClosure hsuZ (hw.2.1.symm.mul_left (Commute.refl u))
    have huL : u ∈ centralizerClosure Z u := by
      have hh := (centralizerClosure Z u).mul_mem hsL hsuL
      simpa only [← mul_assoc, ← pow_two, hsI.sq_eq_one, one_mul] using hh
    exact huZ ((pair_involution_centralizerClosure_involutions h r htM huD hu huL).mp hu)
  have hrv : IsConj s (u * v) := by
    simpa only [hhalf, ← hw.2.2.eq] using (DihedralHalfOrderClasses.exchange hs2 hv2 hmod).2
  have hrZ := mem_Z_of_isConj h hsZ hrv
  have hrL : u * v ∈ centralizerClosure Z u :=
    mem_centralizerClosure hrZ ((Commute.refl u).mul_left hw.2.2.symm)
  have hr2 : orderOf (u * v) = 2 := orderOf_eq_prime (h.involutions _ hrZ).sq_eq_one (h.involutions _ hrZ).ne_one
  refine ⟨hrL, hsL, hr2, hs2, ?_⟩
  have hodd : Odd (orderOf (s * v) / 2) := by
    exact ⟨orderOf (s * v) / 4, by omega⟩
  apply hodd.of_dvd_nat
  apply orderOf_dvd_of_pow_eq_one
  have heq : (u * v) * s = u * (s * v)⁻¹ := by
    rw [mul_inv_rev, hsI.inv_eq_self, hvI.inv_eq_self, mul_assoc]
  rw [heq, ((hw.2.1.mul_right hw.2.2).inv_right).mul_pow,
    involution_pow_odd hu.sq_eq_one hodd, inv_pow]
  rw [← halfOrder_def, hhalf, mul_inv_cancel]

/-- The source correspondence between the actual mixed fiber and local odd-product pairs. -/
public def residual_fiber_equiv_local_odd_pairs
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (htM : t ∉ M)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hshear : ∀ a ∈ Z, Commute u a → IsConj u (u * a)) :
    Fiber z u u ≃ ResidualCentralizerOddPairs Z u where
  toFun p := by
    have hp := fiber_local_pair h r hz htM huD hu p
    exact ⟨(⟨u * p.val.2, hp.1⟩, ⟨p.val.1, hp.2.1⟩),
      (orderOf_coe _).symm.trans hp.2.2.1,
      (orderOf_coe _).symm.trans hp.2.2.2.1,
      by rw [← orderOf_coe]; exact hp.2.2.2.2⟩
  invFun p := by
    let a := p.val.1
    let b := p.val.2
    have haZ : (a : G) ∈ Z := mem_Z_of_isConj h hz
      (isConj_of_local_involution h r hz htM huD hu a p.property.1)
    have hbZ : (b : G) ∈ Z := mem_Z_of_isConj h hz
      (isConj_of_local_involution h r hz htM huD hu b p.property.2.1)
    have hua : Commute u (a : G) := (mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u a.property)).symm
    have hub : Commute u (b : G) := (mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u b.property)).symm
    have hconj := hshear a haZ hua
    refine ⟨((b : G), u * (a : G)),
      isConj_of_local_involution h r hz htM huD hu b p.property.2.1, hconj, ?_⟩
    rw [halfOrder_def]
    have heq : (b : G) * (u * a) = u * ((b : G) * a) := by rw [← mul_assoc, ← hub.eq, mul_assoc]
    rw [heq]
    apply half_power_mul_odd hu (hub.mul_right hua)
    have ho : Odd (orderOf (((a : G) * b)⁻¹)) := by
      rw [orderOf_inv, ← coe_mul, orderOf_coe]
      exact p.property.2.2
    simpa only [mul_inv_rev, (h.involutions _ haZ).inv_eq_self, (h.involutions _ hbZ).inv_eq_self] using ho
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change u * (u * p.val.2) = p.val.2
      rw [← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change u * (u * (p.val.1 : G)) = (p.val.1 : G)
      rw [← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul]
    · rfl

section Specifications
variable (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
  {z t u : G} (hz : z ∈ Z) (htM : t ∉ M)
  (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
  (hshear : ∀ a ∈ Z, Commute u a → IsConj u (u * a))

/-- The forward map retains the source's order of the local factors. -/
public theorem residual_fiber_equiv_local_odd_pairs_apply (p : Fiber z u u) :
    let e := residual_fiber_equiv_local_odd_pairs h r hz htM huD hu hshear
    (((e p).val.1 : G), ((e p).val.2 : G)) = (u * p.val.2, p.val.1) := by rfl

/-- The inverse map retains the repository's ordered `(distinguished, actor)` fiber. -/
public theorem residual_fiber_equiv_local_odd_pairs_symm_apply
    (p : ResidualCentralizerOddPairs Z u) :
    let e := residual_fiber_equiv_local_odd_pairs h r hz htM huD hu hshear
    (e.symm p).val = ((p.val.2 : G), u * (p.val.1 : G)) := by rfl
end Specifications

end ResidualFiberCorrespondence

/-- The actor's actual Thompson fiber counts ordered odd-product involution
pairs in its distinguished centralizer closure. No initial commutation of
`z` and `u`, or centralizer collapse, is required. -/
public theorem proper_residualGenerated_kappa_actor_eq_local_odd_pairs
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t u : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    kappa z u u = Nat.card (ResidualCentralizerOddPairs Z u) := by
  have hk : kappa z u u = Nat.card (Fiber z u u) := by
    simp only [kappa_def, Fiber, halfOrder_def]
  rw [hk]
  exact Nat.card_congr (ResidualFiberCorrespondence.residual_fiber_equiv_local_odd_pairs
    h.disconnected r hz htM huD hu (fun a haZ hcomm =>
      proper_residualGenerated_commuting_mixed_fusion_of_local
        h r ha hz hzM ht htM hL heven hlocal huD hu (IsConj.refl u) haZ hcomm))

end BenderSuzuki.ZD
