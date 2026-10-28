module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Localization.Degree.Support
public import Theory.GroupTheory.TwoInvolutionClassOrder.SingletonCommuting

/-!
# The single shearing fusion in the linear degree argument

Let L be the proper residual subgroup, containing the distinguished root A,
and suppose its ambient centralizer J has order two. Assume the permitted
collapse C_G(v)° = L for involutions v in the two-point stabilizer D.
The nonidentity element u of J is conjugate to uz.

Local strong embedding and fusion in M put every mixed half-order involution
in the class of uz, without assuming shearing. If u and uz were not conjugate,
double transitivity and collapse would force C_G(uz) into M: any involution
in M whose centralizer leaves M is conjugate into D and hence into J.
Fusion control then shows that the fiber over uz is the single pair (z,u).
Equivariance forces every mixed pair to commute. Thus u centralizes the
whole distinguished class, contrary to generation and the trivial center.

This proves the precise instance needed from GLS, Volume 4, Chapter 2,
Lemmas 12.6–12.7, `refs/KGroup/GLS4/Chapter2.tex`. The singleton-fiber
argument replaces the source's final centralizer-product count. No matrix
model, stabilizer order, degree, or exhaustion of involution classes is used.
The centralizer-closure collapse remains the explicitly permitted hypothesis;
this module does not assert its earlier-source proof.
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

/-- Commuting mixed products lie in the class of uz. -/
private theorem shearing_commuting_product_class
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hcollapse : centralizerClosure Z u = residualGenerated M z t) :
    ∀ v s : G, IsConj u v → s ∈ Z → Commute v s → IsConj (u * z) (v * s) := by
  have huL (x : residualGenerated M z t) : MulAut.conj (x : G) u = u :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp huJ x x.property)
  have hlocal {s : G} (hs : s ∈ Z) (hc : Commute u s) : IsConj (u * z) (u * s) := by
    have hsL : s ∈ residualGenerated M z t := hcollapse ▸ mem_centralizerClosure hs hc.symm
    have hzL : z ∈ residualGenerated M z t :=
      (show zpowers z ≤ residualGenerated M z t from le_sup_left.trans le_sup_left) (mem_zpowers z)
    obtain ⟨g, hg⟩ := (stronglyEmbedded_in_proper_residualGenerated h r hz hzM ht htM hL).involutions_conjugate
      (BenderSuzuki.IsInvolution.subtype (h.involutions z hz) hzL)
      (BenderSuzuki.IsInvolution.subtype (h.involutions s hs) hsL)
    have hgs : MulAut.conj ((g : G)⁻¹) z = s := by
      simpa only [rightConjugateElem, MulAut.conj_apply,
        coe_mul, coe_inv, inv_inv] using congrArg Subtype.val hg
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
  have hconj : IsConj (u * z) (MulAut.conj g (u * z)) := isConj_iff.mpr ⟨g, rfl⟩
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

/-- Mixed half-order involutions lie in the class of uz, before shearing. -/
private theorem shearing_halfOrder_product_class
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t) :
    ∀ a b : G, IsConj z a → IsConj u b → IsConj (u * z) (halfOrder a b) := by
  have huD := centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM huJ
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM huD
  have huA : u ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) :=
    centralizer_le hAL huJ
  have hP := involutionProducts_eq_distinguished h r hz hzM ht htM hL hAL
  have hs := shearing_commuting_product_class h.disconnected r hz hzM ht htM hL huJ hcollapse
  have hzI := h.disconnected.involutions z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  have hfixed {v : G} (hv : IsConj u v) : IsConj (u * z) (halfOrder z v) := by
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

omit [Finite G] in
private theorem shearing_pair_conjugator (ha : ResidualAction Z M)
    {t v : G} (htM : t ∉ M) (hvM : v ∈ M)
    (hC : ¬ centralizer ({v} : Set G) ≤ M) :
    ∃ m : G, MulAut.conj m v ∈ residualPairStabilizer M t := by
  obtain ⟨g, hgC, hgM⟩ := Set.not_subset.mp hC
  let α : G ⧸ M := QuotientGroup.mk 1
  have hstab : MulAction.stabilizer G α = M := MulAction.stabilizer_quotient M
  have hgα : α ≠ g • α := by
    intro he
    exact hgM (hstab ▸ he.symm)
  have htα : α ≠ t⁻¹ • α := by
    intro he
    apply htM
    rw [← hstab]
    exact (inv_smul_eq_iff.mp he.symm).symm
  obtain ⟨m, hmα, hmg⟩ := MulAction.is_two_pretransitive_iff.mp ha.two_transitive hgα htα
  have hvα : v • α = α := MulAction.mem_stabilizer_iff.mp (hstab.symm ▸ hvM)
  have hvg : v • (g • α) = g • α := by
    rw [← mul_smul, ← mem_centralizer_singleton_iff.mp hgC, mul_smul, hvα]
  have hfix (β : G ⧸ M) (hvβ : v • β = β) :
      MulAut.conj m v • (m • β) = m • β := by
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul, hvβ]
  refine ⟨m, ?_, ?_⟩
  · rw [← hstab]
    exact MulAction.mem_stabilizer_iff.mpr (by simpa only [hmα] using hfix α hvα)
  · rw [← hstab, rightConjugate_stabilizer]
    exact MulAction.mem_stabilizer_iff.mpr (by simpa only [hmg] using hfix (g • α) hvg)

omit [Finite G] in
private theorem shearing_centralizer_confinement
    (ha : ResidualAction Z M) {z t u v : G} (htM : t ∉ M)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ w : G, w ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution w →
      centralizerClosure Z w = residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u) (hv : PFAppendixIII.IsInvolution v) (hvM : v ∈ M)
    (hn : ¬ IsConj u v) : centralizer ({v} : Set G) ≤ M := by
  by_contra hC
  obtain ⟨m, hm⟩ := shearing_pair_conjugator ha htM hvM hC
  have hi := BenderSuzuki.IsInvolution.map_of_injective hv
    (MulAut.conj m).toMonoidHom (MulAut.conj m).injective
  have hc : MulAut.conj m v ∈ centralizer (residualGenerated M z t : Set G) := by
    intro a haL
    have haC : a ∈ centralizer ({MulAut.conj m v} : Set G) :=
      centralizerClosure_le Z _ ((hcollapse _ hm hi).symm ▸ haL)
    exact (mem_centralizer_singleton_iff.mp haC)
  let J := centralizer (residualGenerated M z t : Set G)
  obtain ⟨j, _, hj⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  have he : MulAut.conj m v = u := congrArg Subtype.val
    ((hj ⟨_, hc⟩ (fun he => hi.ne_one (congrArg Subtype.val he))).trans
      (hj ⟨u, huJ⟩ (fun he => hu.ne_one (congrArg Subtype.val he))).symm)
  exact hn ((isConj_iff.mpr ⟨m, he⟩).symm)

private theorem shearing_fiber_singleton
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u)
    (hcollapse : centralizerClosure Z u = residualGenerated M z t)
    (hn : ¬ IsConj u (u * z)) (hC : centralizer ({u * z} : Set G) ≤ M) :
    ∀ p : Fiber z u (u * z), p.val = (z, u) := by
  have huD := centralizer_residualGenerated_le_pairStabilizer h hz hzM huJ
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h htM huD
  have hzu : ¬ IsConj z u := fun hc => huZ (mem_distinguished_of_isConj h hz hc)
  have huA := centralizer_le hAL huJ
  have hcu {a : G} (ha : a ∈ closure (Z ∩ (M : Set G))) : Commute u a :=
    (mem_centralizer_iff.mp huA a ha).symm
  have hzI := h.involutions z hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  intro p
  let a := p.val.1
  let b := p.val.2
  have haZ : a ∈ Z := mem_distinguished_of_isConj h hz p.property.1
  have haI := h.involutions a haZ
  have hbI : PFAppendixIII.IsInvolution b := by
    obtain ⟨g, hg⟩ := isConj_iff.mp p.property.2.1
    have hi := BenderSuzuki.IsInvolution.map_of_injective hu
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    change PFAppendixIII.IsInvolution (g * u * g⁻¹) at hi
    change PFAppendixIII.IsInvolution p.val.2
    rwa [← hg]
  have hm := fiber_mem_centralizer hz2 hu2 hzu p
  have haM : a ∈ M := hC hm.1
  have hbM : b ∈ M := hC hm.2
  have haA : a ∈ closure (Z ∩ (M : Set G)) := subset_closure ⟨haZ, haM⟩
  have hbA := conjugate_centralizes_distinguished h r hu huD.1 huA p.property.2.1 hbM
  have hab : Commute a b := mem_centralizer_iff.mp hbA a haA
  have habI : PFAppendixIII.IsInvolution (a * b) := by
    constructor
    · intro he
      have heab : a = b := by
        simpa only [hbI.inv_eq_self] using eq_inv_iff_mul_eq_one.mpr he
      have heba : p.val.2 = p.val.1 := heab.symm
      exact hzu (p.property.1.trans (heba ▸ p.property.2.1.symm))
    · rw [hab.mul_pow, haI.sq_eq_one, hbI.sq_eq_one, one_mul]
  have hp : a * b = u * z := by
    have ho : orderOf (a * b) = 2 := orderOf_eq_prime habI.sq_eq_one habI.ne_one
    have hf : halfOrder a b = u * z := p.property.2.2
    simpa only [halfOrder_def, ho, Nat.reduceDiv, pow_one] using hf
  have hba : b = (u * z) * a := by
    rw [← hp, hab.eq, mul_assoc, ← pow_two, haI.sq_eq_one, mul_one]
  have hub : Commute u b := by
    rw [hba]
    exact ((Commute.refl u).mul_right (hcu (subset_closure ⟨hz, hzM⟩))).mul_right (hcu haA)
  have hubprod : u * b = z * a := by
    rw [hba, ← mul_assoc, ← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul]
  have hbu : b = u := by
    by_contra hne
    have hprodI : PFAppendixIII.IsInvolution (u * b) := by
      constructor
      · intro he
        have heb : u = b := by
          simpa only [hbI.inv_eq_self] using eq_inv_iff_mul_eq_one.mpr he
        exact hne heb.symm
      · rw [hub.mul_pow, hu.sq_eq_one, hbI.sq_eq_one, one_mul]
    have hprodZ := distinguished_mul_mem_of_involution h r hz hzM ht htM hL hAL
      hz haZ (hubprod ▸ hprodI)
    have hs := shearing_commuting_product_class h r hz hzM ht htM hL huJ hcollapse
      u (u * b) (IsConj.refl u) (hubprod.symm ▸ hprodZ) ((Commute.refl u).mul_right hub)
    have he : u * (u * b) = b := by
      rw [← mul_assoc, ← pow_two, hu.sq_eq_one, one_mul]
    rw [he] at hs
    exact hn (p.property.2.1.trans hs.symm)
  have haz : a = z := by
    rw [hbu] at hp
    have hc : Commute u z := hcu (subset_closure ⟨hz, hzM⟩)
    exact mul_right_cancel (hp.trans hc.eq)
  exact Prod.ext haz hbu

/-- The single fusion required by the linear degree count. -/
public theorem linear_shearing_of_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ w : G, w ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution w →
      centralizerClosure Z w = residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u) : IsConj u (u * z) := by
  by_contra hn
  have huD := centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM huJ
  have huZ := not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM huD
  have hcu : Commute u z :=
    (mem_centralizer_iff.mp huJ z (hAL (subset_closure ⟨hz, hzM⟩))).symm
  have hzI := h.disconnected.involutions z hz
  have huz : PFAppendixIII.IsInvolution (u * z) := by
    constructor
    · intro he
      have heuz : u = z := by
        simpa only [hzI.inv_eq_self] using eq_inv_iff_mul_eq_one.mpr he
      exact huZ (heuz.symm ▸ hz)
    · rw [hcu.mul_pow, hu.sq_eq_one, hzI.sq_eq_one, one_mul]
  have hcl := hcollapse u huD hu
  have hC := shearing_centralizer_confinement ha htM hJ hcollapse huJ hu huz
    (M.mul_mem huD.1 hzM) hn
  have hs := shearing_halfOrder_product_class h r hz hzM ht htM hL hAL huJ hu hcl
  have hf := shearing_fiber_singleton h.disconnected r hz hzM ht htM hL hAL huJ hu hcl hn hC
  have hgen : closure Z ≤ centralizer ({u} : Set G) := by
    rw [closure_le]
    intro a haZ
    exact mem_centralizer_singleton_iff.mpr
      (commute_of_singleton_halfOrder_fiber z u (u * z) hcu.symm hs hf
        (r.one_class z hz a haZ) (IsConj.refl u)).eq
  have htop : centralizer ({u} : Set G) = ⊤ := top_le_iff.mp (r.generated ▸ hgen)
  have huC : u ∈ center G := centralizer_eq_top_iff_subset.mp htop (Set.mem_singleton u)
  rcases r.simple.eq_bot_or_eq_top_of_normal (center G) inferInstance with hc | hc
  · exact hu.ne_one (mem_bot.mp (hc ▸ huC))
  · have hzC : z ∈ center G := hc ▸ mem_top z
    exact htM (h.disconnected.centralizer_le hz hzM
      (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzC t)))

/-- Apply the proved shearing fusion to the literal mixed-fiber support used
by the degree assembly, under the permitted centralizer-closure collapse. -/
public theorem linear_halfOrder_support_of_centralizerClosure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t u : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hcollapse : ∀ w : G, w ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution w →
      centralizerClosure Z w = residualGenerated M z t)
    (huJ : u ∈ centralizer (residualGenerated M z t : Set G))
    (hu : PFAppendixIII.IsInvolution u) :
    ∀ a b : G, IsConj z a → IsConj u b → IsConj u (halfOrder a b) := by
  have huD := centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM huJ
  exact linear_halfOrder_support_of_one_fusion h r hz hzM ht htM hL hAL huJ hu
    (hcollapse u huD hu)
    (linear_shearing_of_centralizerClosure h r ha hz hzM ht htM hL hAL hJ hcollapse huJ hu)
end BenderSuzuki.ZD
