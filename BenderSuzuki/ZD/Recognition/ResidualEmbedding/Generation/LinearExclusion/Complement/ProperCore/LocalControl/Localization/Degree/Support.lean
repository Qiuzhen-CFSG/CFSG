module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.Setup
public import Theory.GroupTheory.DihedralHalfOrderClasses
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Linear mixed-fiber support from one shearing fusion

Assume that the selected centralizer involution u is conjugate to uz. Local
strong embedding in L propagates this equality to every commuting mixed pair.
If a mixed product had order divisible by four, its half-order involution would
belong to the distinguished class, by the proved involution-product equality.
Its centralizer forces the other reflection into M. Fusion in M then forces
that reflection to centralize the root, contradicting the product order.
The remaining dihedral reflection formula and shearing put the canonical
involution in the class of u.

The one fusion `u ~ uz` remains an explicit source obligation. No global
exhaustion by two involution classes, and hence no use of the later Lemma 12.11,
is made. Source: GLS, Volume 4, Chapter 2, Lemmas 12.7–12.8(a),
`refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 TwoInvolutionClassOrder
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem mem_distinguished_of_isConj (h : IsProductDisconnected Z M)
    {a b : G} (ha : a ∈ Z) (hab : IsConj a b) : b ∈ Z := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  exact hg ▸ h.invariant g a ha

/-- One shearing equality propagates to all commuting mixed pairs. -/
public theorem linear_shear_commuting_of_one_fusion
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hshear : IsConj u (u * z)) :
    ∀ v s : G, IsConj u v → s ∈ Z → Commute v s → IsConj u (v * s) := by
  have huL (x : residualGenerated M z t) : MulAut.conj (x : G) u = u :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp huJ x x.property)
  have hlocal {s : G} (hs : s ∈ Z) (hc : Commute u s) : IsConj u (u * s) := by
    have hsL : s ∈ residualGenerated M z t := hcollapse ▸ mem_centralizerClosure hs hc.symm
    have hzL : z ∈ residualGenerated M z t :=
      (show zpowers z ≤ residualGenerated M z t from le_sup_left.trans le_sup_left) (mem_zpowers z)
    obtain ⟨g, hg⟩ := (stronglyEmbedded_in_proper_residualGenerated h r hz hzM ht htM hL).involutions_conjugate
      (BenderSuzuki.IsInvolution.subtype (h.involutions z hz) hzL)
      (BenderSuzuki.IsInvolution.subtype (h.involutions s hs) hsL)
    have hgs : MulAut.conj ((g : G)⁻¹) z = s := by
      simpa only [rightConjugateElem, MulAut.conj_apply,
        coe_mul, coe_inv, inv_inv] using congrArg Subtype.val hg
    apply hshear.trans
    apply isConj_iff.mpr
    refine ⟨(g : G)⁻¹, ?_⟩
    change MulAut.conj ((g : G)⁻¹) (u * z) = _
    rw [map_mul, hgs, show MulAut.conj ((g : G)⁻¹) u = u from huL g⁻¹]
  intro v s hv hs hc
  obtain ⟨g, rfl⟩ := isConj_iff.mp hv
  have hgsZ : MulAut.conj g⁻¹ s ∈ Z := h.invariant g⁻¹ s hs
  have hcomm : Commute u (MulAut.conj g⁻¹ s) := by
    simpa [MulAut.conj_apply, mul_assoc] using hc.map (MulAut.conj g⁻¹).toMonoidHom
  have hh := (MulAut.conj g).toMonoidHom.map_isConj (hlocal hgsZ hcomm)
  have hconj : IsConj u (MulAut.conj g u) := isConj_iff.mpr ⟨g, rfl⟩
  apply hconj.trans
  simpa [MulAut.conj_apply, mul_assoc] using hh

private theorem conjugate_centralizes_distinguished
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {u v : G} (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hv : IsConj u v) (hvM : v ∈ M) :
    v ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
  have hvI : PFAppendixIII.IsInvolution v := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hv
    exact BenderSuzuki.IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  obtain ⟨S, hSM, hf⟩ := r.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hu hvI huM hvM hv
  intro a ha
  have hmN : (m : G)⁻¹ ∈ normalizer (closure (Z ∩ (M : Set G)) : Set G) := by
    rw [distinguishedClosure_normalizer h]
    exact M.inv_mem m.property
  have haA : (m : G)⁻¹ * a * m ∈ closure (Z ∩ (M : Set G)) := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp hmN a).mp ha
  have hh := congrArg (MulAut.conj (m : G)) (mem_centralizer_iff.mp huA _ haA)
  have hmu : MulAut.conj (m : G) u = v := hm
  have hma : MulAut.conj (m : G) ((m : G)⁻¹ * a * m) = a := by
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [map_mul, hmu, hma] using hh

/-- The source's commuting case has one-class mixed-fiber support. This assumes
only the one shearing fusion, not exhaustion of all ambient involutions. -/
public theorem linear_halfOrder_support_of_one_fusion
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hshear : IsConj u (u * z)) :
    ∀ a b : G, IsConj z a → IsConj u b → IsConj u (halfOrder a b) := by
  have huD := centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM huJ
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM huD
  have huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) :=
    centralizer_le hAL huJ
  have hP := involutionProducts_eq_distinguished h r hz hzM ht htM hL hAL
  have hs := linear_shear_commuting_of_one_fusion h.disconnected r hz hzM ht htM hL huJ hcollapse hshear
  have hzI := h.disconnected.involutions z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have hfixed {v : G} (hv : IsConj u v) : IsConj u (halfOrder z v) := by
    have hvZ : v ∉ Z := fun hvZ => huZ (mem_distinguished_of_isConj h.disconnected hvZ hv.symm)
    have hvI : PFAppendixIII.IsInvolution v := by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hv
      exact BenderSuzuki.IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hv2 : orderOf v = 2 := orderOf_eq_prime hvI.sq_eq_one hvI.ne_one
    have hnv : ¬ IsConj z v := fun hh => hvZ (mem_distinguished_of_isConj h.disconnected hz hh)
    have hw := halfOrder_properties hz2 hv2 hnv (IsConj.refl z) (IsConj.refl v)
    have heven : Even (orderOf (z * v)) := by
      apply Nat.not_odd_iff_even.mp
      exact fun ho => hnv (isConj_of_involutions_odd_product z v hzI.sq_eq_one hvI.sq_eq_one ho)
    have hmod : orderOf (z * v) % 4 = 2 := by
      by_contra hn
      have hdiv : orderOf (z * v) % 4 = 0 := by obtain ⟨k, hk⟩ := heven; omega
      have hzwZ := mem_distinguished_of_isConj h.disconnected hz
        (DihedralHalfOrderClasses.preserve hz2 hv2 hdiv).1
      have hwZ : halfOrder z v ∈ Z := by
        rw [← hP]
        refine ⟨(orderOf_eq_prime_iff.mp hw.1).symm, z, hz, z * halfOrder z v, hzwZ, ?_⟩
        rw [← mul_assoc, ← pow_two, hzI.sq_eq_one, one_mul]
      have hwM : halfOrder z v ∈ M := mem_of_commute h.disconnected hz hzM hw.2.1.symm
      have hvM := mem_of_commute h.disconnected hwZ hwM hw.2.2
      have hvc := conjugate_centralizes_distinguished h.disconnected r hu huD.1 huA hv hvM
      have hcz : Commute z v := mem_centralizer_iff.mp hvc z (subset_closure ⟨hz, hzM⟩)
      have hp : (z * v) ^ 2 = 1 := by rw [hcz.mul_pow, hzI.sq_eq_one, hvI.sq_eq_one, one_mul]
      have hd := orderOf_dvd_of_pow_eq_one hp
      have hl := Nat.le_of_dvd (by decide : 0 < 2) hd
      have hpos := orderOf_pos (z * v)
      omega
    have hvwZ := mem_distinguished_of_isConj h.disconnected hz
      (DihedralHalfOrderClasses.exchange hz2 hv2 hmod).2
    have hc : Commute v (v * halfOrder z v) := (Commute.refl v).mul_right hw.2.2.symm
    have hh := hs v (v * halfOrder z v) hv hvwZ hc
    simpa only [← mul_assoc, ← pow_two, hvI.sq_eq_one, one_mul] using hh
  intro a b ha hb
  obtain ⟨g, hg⟩ := isConj_iff.mp ha.symm
  have hgb : IsConj u (MulAut.conj g b) := hb.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hh := hfixed hgb
  have he : halfOrder z (MulAut.conj g b) = MulAut.conj g (halfOrder a b) := by
    rw [← hg]
    exact halfOrder_map (MulAut.conj g) a b
  rw [he] at hh
  exact hh.trans (isConj_iff.mpr ⟨g, rfl⟩).symm
end BenderSuzuki.ZD
