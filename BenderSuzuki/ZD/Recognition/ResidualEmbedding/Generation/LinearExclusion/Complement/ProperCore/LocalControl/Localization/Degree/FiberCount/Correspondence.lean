module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.Support

/-!
# The actual mixed-involution fiber as local odd-product pairs

With the repository's ordered fiber `(s,v)`, the source correspondence is
`(s,v) ↦ (uv,s)`, with inverse `(a,b) ↦ (b,ua)`. Fiber centralizer containment
puts `s` in the selected local subgroup. The dihedral half-order identities
exclude product order divisible by four and put `uv` in the distinguished
class. The remaining half-order exponent is odd, giving the odd local product.
Conversely, the single shearing fusion puts `ua` in the class of `u`, and
coprime commuting element orders verify the literal half-order equation.

This establishes the correspondence without assuming any local cardinality,
matrix model, coset degree, or exhaustion of ambient involution classes.
Source: GLS, Volume 4, Chapter 2, Lemma 12.8(a),
`refs/KGroup/GLS4/Chapter2.tex`, the calculation of `a(u)`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

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
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (x : residualGenerated M z t) (hx : orderOf x = 2) : IsConj z (x : G) := by
  have hzL : z ∈ residualGenerated M z t :=
    (show zpowers z ≤ residualGenerated M z t from le_sup_left.trans le_sup_left) (mem_zpowers z)
  have hxI : PFAppendixIII.IsInvolution x := (orderOf_eq_prime_iff.mp hx).symm
  obtain ⟨g, hg⟩ := (stronglyEmbedded_in_proper_residualGenerated h r hz hzM ht htM hL).involutions_conjugate
    (BenderSuzuki.IsInvolution.subtype (h.involutions z hz) hzL) hxI
  exact isConj_iff.mpr ⟨(g : G)⁻¹, by
    simpa only [rightConjugateElem, MulAut.conj_apply,
      coe_mul, coe_inv, inv_inv] using congrArg Subtype.val hg⟩

private theorem fiber_local_pair
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (p : Fiber z u u) :
    u * p.val.2 ∈ residualGenerated M z t ∧ p.val.1 ∈ residualGenerated M z t ∧
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
    (centralizer_residualGenerated_le_pairStabilizer h hz hzM huJ)
  have hnot : ¬ IsConj z u := fun he => huZ (mem_Z_of_isConj h hz he)
  have hw := halfOrder_properties hz2 hu2 hnot p.property.1 p.property.2.1
  rw [p.property.2.2] at hw
  change orderOf u = 2 ∧ Commute u s ∧ Commute u v at hw
  have hsL : s ∈ residualGenerated M z t :=
    hcollapse ▸ mem_centralizerClosure hsZ hw.2.1.symm
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
    have hsuL : s * u ∈ residualGenerated M z t := hcollapse ▸
      mem_centralizerClosure hsuZ (hw.2.1.symm.mul_left (Commute.refl u))
    have huL : u ∈ residualGenerated M z t := by
      have hh := (residualGenerated M z t).mul_mem hsL hsuL
      simpa only [← mul_assoc, ← pow_two, hsI.sq_eq_one, one_mul] using hh
    exact huZ ((isInvolution_iff_mem_Z_in_proper_residualGenerated h r hz hzM ht htM hL huL).mp hu)
  have hrv : IsConj s (u * v) := by
    simpa only [hhalf, ← hw.2.2.eq] using (DihedralHalfOrderClasses.exchange hs2 hv2 hmod).2
  have hrZ := mem_Z_of_isConj h hsZ hrv
  have hrL : u * v ∈ residualGenerated M z t := hcollapse ▸
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
public def linear_fiber_equiv_odd_pairs
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hshear : IsConj u (u * z)) :
    Fiber z u u ≃ {p : residualGenerated M z t × residualGenerated M z t //
      orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} where
  toFun p := by
    have hp := fiber_local_pair h r hz hzM ht htM hL huJ hu hcollapse p
    exact ⟨(⟨u * p.val.2, hp.1⟩, ⟨p.val.1, hp.2.1⟩),
      (orderOf_coe _).symm.trans hp.2.2.1,
      (orderOf_coe _).symm.trans hp.2.2.2.1,
      by rw [← orderOf_coe]; exact hp.2.2.2.2⟩
  invFun p := by
    let a := p.val.1
    let b := p.val.2
    have haZ : (a : G) ∈ Z := mem_Z_of_isConj h hz
      (isConj_of_local_involution h r hz hzM ht htM hL a p.property.1)
    have hbZ : (b : G) ∈ Z := mem_Z_of_isConj h hz
      (isConj_of_local_involution h r hz hzM ht htM hL b p.property.2.1)
    have hua : Commute u (a : G) := (mem_centralizer_iff.mp huJ a a.property).symm
    have hub : Commute u (b : G) := (mem_centralizer_iff.mp huJ b b.property).symm
    have hconj := linear_shear_commuting_of_one_fusion h r hz hzM ht htM hL huJ hcollapse hshear
      u a (IsConj.refl u) haZ hua
    refine ⟨((b : G), u * (a : G)),
      isConj_of_local_involution h r hz hzM ht htM hL b p.property.2.1, hconj, ?_⟩
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
  {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
  (hL : residualGenerated M z t ≠ ⊤)
  (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
  (hu : PFAppendixIII.IsInvolution u)
  (hcollapse : centralizerClosure Z u = residualGenerated M z t)
  (hshear : IsConj u (u * z))

/-- The forward correspondence uses the source's order of the two local factors. -/
public theorem linear_fiber_equiv_odd_pairs_apply (p : Fiber z u u) :
    let e := linear_fiber_equiv_odd_pairs h r hz hzM ht htM hL huJ hu hcollapse hshear
    (((e p).val.1 : G), ((e p).val.2 : G)) = (u * p.val.2, p.val.1) := by rfl

/-- The inverse correspondence retains the repository's `(s,v)` fiber convention. -/
public theorem linear_fiber_equiv_odd_pairs_symm_apply
    (p : {p : residualGenerated M z t × residualGenerated M z t //
      orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))}) :
    let e := linear_fiber_equiv_odd_pairs h r hz hzM ht htM hL huJ hu hcollapse hshear
    (e.symm p).val = ((p.val.2 : G), u * (p.val.1 : G)) := by rfl

include h r hz hzM ht htM hL huJ hu hcollapse hshear in
/-- The Thompson fiber counts exactly the local odd-product involution pairs. -/
public theorem linear_kappa_eq_odd_pairs :
    kappa z u u = Nat.card {p : residualGenerated M z t × residualGenerated M z t //
      orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} := by
  have hk : kappa z u u = Nat.card (Fiber z u u) := by
    change kappa z u u = Nat.card {p : G × G //
      IsConj z p.1 ∧ IsConj u p.2 ∧ halfOrder p.1 p.2 = u}
    simp only [kappa_def, halfOrder_def]
  rw [hk]
  exact Nat.card_congr (linear_fiber_equiv_odd_pairs h r hz hzM ht htM hL huJ hu hcollapse hshear)
end Specifications
end BenderSuzuki.ZD
