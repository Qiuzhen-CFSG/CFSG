module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.ElementaryRank.Automorphisms
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.Distinguished
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl.Torus
public import Theory.GroupTheory.TorusInvolutionSaturation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.InvolutionBase.InvolutionBounds.Census

/-!
# Elementary rank in the linear centralizer closure

Write A = M°, J = C_G(L), R = ⟨Jᴹ⟩, and K = D ∩ L, all internally in M.
Localization C_R(J) ≤ AJ and the orders |R| = 2q², |A| = q, |J| = 2
first show that R has a noninvolution. Its nontrivial square lies in A.
The free K-action on A then yields q(q-1) distinct noninvolutions in R.
The proved census supplies q² conjugates of the involution u of J. Together
with A these exhaust the square-one elements of R, proving M-fusion.

For an elementary E crossing A, conjugate one of its outside involutions
to u. The conjugated E centralizes u and hence normalizes the literal L,
by C_G(u)° = L. The actual conjugation homomorphism has kernel in J;
the genuine PSL₂ automorphism rank gives |E| ≤ 2q.

The final theorem supplies the elementary-subgroup bound consumed by
`linear_involutionBase_of_torus_section_and_involution_bounds`. It discharges
the earlier orbit-count input using the independent census. Only the
permitted centralizer-closure, supplement, and earlier section premises
remain; no fusion, representation, kernel bound, or abelian base is assumed.
Source: GLS, Volume 4, Chapter 2, end of Lemma 15.6 and first paragraph
of Lemma 15.7, `refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2745.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Localization and the order of R rule out exponent two, without first
knowing anything about the abelian base. -/
public theorem linearCentralizerClosure_has_noninvolution
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t) :
    ∃ x ∈ linearCentralizerClosure M z t, x ^ 2 ≠ 1 := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let R := linearCentralizerClosure M z t
  let : A.Normal := distinguishedClosure_normal h
  have hJR : J ≤ R := subset_normalClosure
  have hRV := linearCentralizerClosure_le_twoCore hR
  obtain ⟨_, _, hAc⟩ := linear_distinguishedClosure_internal_facts h r hz hzM ht htM hL hn e hAL
  have hJc := linearCentralizer_subgroupOf_card h hz hzM hJ
  have hlocal := linear_involution_localization_of_centralizerClosure h r hz hzM ht htM hL hn e
    hAL hJ hcollapse
  by_contra hnon
  have hs : ∀ x ∈ R, x ^ 2 = 1 := by simpa only [not_exists, not_and, not_not] using hnon
  have hc : ∀ x y : R, Commute x y := Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (Subtype.ext (hs x x.property)))
  have hle : R ≤ A ⊔ J := by
    intro x hx
    apply hlocal
    refine ⟨hRV hx, ?_⟩
    intro j hj
    exact congrArg Subtype.val (hc ⟨j, hJR hj⟩ ⟨x, hx⟩).eq
  have hcard := card_le_of_le hle
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A J le_normalizer_of_normal
  have hpos : 0 < Nat.card (A ⊓ J : Subgroup M) := Nat.card_pos
  change Nat.card R ≤ Nat.card (A ⊔ J : Subgroup M) at hcard
  change Nat.card A = 2 ^ n at hAc
  change Nat.card J = 2 at hJc
  rw [hAc, hJc] at hprod
  rw [hR] at hcard
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  nlinarith

/-- The free torus on the distinguished layer supplies q(q-1) noninvolutions
in R, before any abelian-base conclusion. -/
public theorem linearCentralizerClosure_noninvolution_card_ge
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAR : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCentralizerClosure M z t)
    (hsq : ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M) :
    2 ^ n * (2 ^ n - 1) ≤ Nat.card {x : linearCentralizerClosure M z t // x ^ 2 ≠ 1} := by
  obtain ⟨hAsq, hAc, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h.disconnected r hz hzM ht htM hL hn e hAL
  obtain ⟨hKcard, hfree⟩ := linear_distinguishedClosure_torus_geometry
    h r hz hzM ht htM hL hn e hAL
  obtain ⟨x, hx, hx2⟩ := linearCentralizerClosure_has_noninvolution
    h.disconnected r hz hzM ht htM hL hn e hAL hJ hR hcollapse
  let : (linearCentralizerClosure M z t).Normal := Subgroup.normalClosure_normal
  have hbound := noninvolution_card_ge_of_free_square_orbit
    (linearCentralizerClosure M z t) ((closure (Z ∩ (M : Set G))).subgroupOf M)
    ((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M)
    hAR hAsq (fun a ha x hx => (mem_centralizer_iff.mp (hAc ha) x
      (linearCentralizerClosure_le_twoCore hR hx)).symm) hfree hx (hsq x hx) hx2
  simpa only [hKcard, hAcard, Nat.mul_comm] using hbound

/-- Saturating R with the actual M-class of u proves the fusion required in
GLS 15.7. The orbit count is the independent census producer's sole input. -/
public theorem linearCentralizerClosure_involution_fusion_of_orbit_card
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAR : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCentralizerClosure M z t)
    (hsq : ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M)
    (u : M) (huJ : u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hu : u ≠ 1)
    (horbit : (2 ^ n) ^ 2 ≤ Nat.card {x : linearCentralizerClosure M z t // IsConj u (x : M)}) :
    ∀ x ∈ linearCentralizerClosure M z t, x ^ 2 = 1 →
      x ∉ (closure (Z ∩ (M : Set G))).subgroupOf M → IsConj u x := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let R := linearCentralizerClosure M z t
  let : A.Normal := distinguishedClosure_normal h.disconnected
  obtain ⟨hAsq, _, hAcard⟩ := linear_distinguishedClosure_internal_facts
    h.disconnected r hz hzM ht htM hL hn e hAL
  have hu2 : u ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨u, huJ⟩ : centralizer (residualGenerated M z t : Set G)))
    rw [hJ] at hh
    exact Subtype.ext (congrArg (fun v : centralizer (residualGenerated M z t : Set G) => (v : G)) hh)
  have huG : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  have huA : u ∉ A := by
    intro huA
    have huZ := (isInvolution_iff_mem_Z_in_proper_residualGenerated h.disconnected r
      hz hzM ht htM hL (hAL huA)).mp ⟨huG, congrArg Subtype.val hu2⟩
    exact not_mem_Z_of_mem_residualPairStabilizer h.disconnected htM
      (centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM huJ) huZ
  have hnon := linearCentralizerClosure_noninvolution_card_ge h r hz hzM ht htM hL hn e
    hAL hJ hR hcollapse hAR hsq
  have hP := square_one_mem_of_saturated_card R A (by positivity) hAR hR hAcard hAsq hnon
    (fun x => IsConj u (x : M)) (by
      intro x hx
      obtain ⟨m, hm⟩ := isConj_iff.mp hx
      apply Subtype.ext
      change (x : M) ^ 2 = 1
      rw [← hm, ← MulAut.conj_apply, ← map_pow, hu2, map_one]) (by
      intro x hx hxA
      obtain ⟨m, hm⟩ := isConj_iff.mp hx
      have hh := (inferInstance : A.Normal).conj_mem (x : M) hxA m⁻¹
      apply huA
      rw [← hm] at hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using hh)
    horbit
  intro x hx hx2 hxA
  exact hP ⟨x, hx⟩ (Subtype.ext hx2) hxA

/-- The elementary-centralizer premise of the involution-base consumer.
The census is still explicit; fusion, the automorphism action, its kernel,
and the PSL₂ rank estimate are proved here. -/
public theorem linear_elementary_crossing_card_le_of_orbit_card_and_section
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAB : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t)
    (hsq : ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M)
    (hcensus : ∃ u : M,
      u ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M ∧ u ≠ 1 ∧
      (2 ^ n) ^ 2 ≤ Nat.card {x : linearCentralizerClosure M z t // IsConj u (x : M)}) :
    ∀ E : Subgroup M, E ≤ linearCentralizerClosure M z t →
      (∀ x ∈ E, x ^ 2 = 1) → ¬ E ≤ (closure (Z ∩ (M : Set G))).subgroupOf M →
      Nat.card E ≤ 2 * 2 ^ n := by
  obtain ⟨u, huJ, hu, horbit⟩ := hcensus
  have hAR := hAB.trans (linearCommutatorKernel_le_closure (M := M) (z := z) (t := t))
  have hfusion := linearCentralizerClosure_involution_fusion_of_orbit_card h r hz hzM ht htM hL
    hn e hAL hJ hR hcollapse hAR hsq u huJ hu horbit
  have hu2 : (u : G) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨u, huJ⟩ : centralizer (residualGenerated M z t : Set G)))
    rw [hJ] at hh
    exact congrArg (fun v : centralizer (residualGenerated M z t : Set G) => (v : G)) hh
  have hcl := hcollapse u
    (centralizer_residualGenerated_le_pairStabilizer h.disconnected hz hzM huJ)
    ⟨fun he => hu (Subtype.ext he), hu2⟩
  intro E hER hE hEA
  obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hEA
  obtain ⟨m, hm⟩ := isConj_iff.mp (hfusion x (hER hx) (hE x hx) hxA)
  let f := MulAut.conj m⁻¹
  let E' := E.map f.toMonoidHom
  have hfx : f x = u := by
    rw [← hm]
    simp [f, mul_assoc]
  have hpow (a : E) : a ^ 2 = 1 := Subtype.ext (hE a a.property)
  have hcomm (a : M) (ha : a ∈ E) : Commute a x :=
    (Commute.of_orderOf_dvd_two (fun a : E => orderOf_dvd_of_pow_eq_one (hpow a))
      ⟨a, ha⟩ ⟨x, hx⟩).map E.subtype
  have hE' : ∀ a ∈ E', a ^ 2 = 1 := by
    rintro a ⟨b, hb, rfl⟩
    rw [← map_pow, hE b hb, map_one]
  have hEu : ∀ a ∈ E', Commute (a : G) (u : G) := by
    rintro a ⟨b, hb, rfl⟩
    have hc := (hcomm b hb).map f.toMonoidHom
    change Commute (f b) (f x) at hc
    rw [hfx] at hc
    exact hc.map M.subtype
  have hbound := linear_elementary_involution_centralizer_card_le h.disconnected hn e hJ hcl E' hE' hEu
  have hc : Nat.card E' = Nat.card E := card_map_of_injective f.injective
  exact hc ▸ hbound

/-- Every elementary subgroup of R crossing the distinguished closure has
order at most 2q. The earlier census proves the orbit input, saturation
proves fusion, and actual conjugation on the PSL₂ model supplies the bound. -/
public theorem linear_elementary_crossing_card_le_of_centralizerClosure_and_section
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hcollapse : ∀ u : G, u ∈ residualPairStabilizer M t → PFAppendixIII.IsInvolution u →
      centralizerClosure Z u = residualGenerated M z t)
    (hAB : (closure (Z ∩ (M : Set G))).subgroupOf M ≤ linearCommutatorKernel M z t)
    (hsq : ∀ x ∈ linearCentralizerClosure M z t,
      x ^ 2 ∈ (closure (Z ∩ (M : Set G))).subgroupOf M) :
    ∀ E : Subgroup M, E ≤ linearCentralizerClosure M z t →
      (∀ x ∈ E, x ^ 2 = 1) → ¬ E ≤ (closure (Z ∩ (M : Set G))).subgroupOf M →
      Nat.card E ≤ 2 * 2 ^ n := by
  apply linear_elementary_crossing_card_le_of_orbit_card_and_section h r hz hzM ht htM hL hn e
    hAL hJ hR hcollapse hAB hsq
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  have hJc : Nat.card J = 2 := linearCentralizer_subgroupOf_card h.disconnected hz hzM hJ
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJc
  have huM : (u : M) ≠ 1 := fun he => hu (Subtype.ext he)
  obtain ⟨hcount, hclass⟩ := linear_involution_conjugacy_census_of_centralizerClosure_and_supplement
    h r ha hz hzM ht htM hL hn e hJ hR hAL hDN hDV hcollapse u.property huM
  refine ⟨u, u.property, huM, ?_⟩
  let f : (ConjClasses.mk (u : M)).carrier →
      {x : linearCentralizerClosure M z t // IsConj (u : M) (x : M)} := fun x =>
    ⟨⟨x, (hclass x x.property).1⟩,
      (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp x.property)).symm⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg
      (fun a : {x : linearCentralizerClosure M z t // IsConj (u : M) (x : M)} => (a.val : M)) he)
  exact hcount ▸ Nat.card_le_card_of_injective f hf
end BenderSuzuki.ZD
