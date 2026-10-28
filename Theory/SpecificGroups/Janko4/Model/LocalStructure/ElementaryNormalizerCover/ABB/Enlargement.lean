module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.ABB.Octads
/-!
# Canonical zero-form enlargement for the fixed-point-free pair

A permutation centralizing the marked fixed-point-free involution permutes
its fifteen invariant octads. The incidence profiles recover its six tetrads,
so the quotient centralizer fixes the native kernel involution with mask 818.
For every involution in the seed-pair stabilizer, its fixed octad (or empty
fixed set) makes the seed pair and companion pair have the same inner-half
character. Their product, mask 818, is therefore orthogonal to the canonical
central omega of the full ambient centralizer.

Consequently an elementary group containing the original seed and the marked
fixed-point-free quotient pair has a NONTRIVIAL zero-form subgroup normalized
by its whole normalizer. This supplies the weak ABB(3) enlargement required
at the opening of KW Section 2.3, without assuming nondegeneracy excludes the
configuration or adding an extraspecial-container hypothesis.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), printed p.492
and Corollary 2.3.7, p.493. Native pair labels and Witt octads retain the ATLAS
coordinates and attribution of the imported model.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.ABB
open Cardinality QuotientCount.Image KernelCount
open LinearFive InvolutionCentralizers.Second ElementaryEightGeometry
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LargeCenterRadicals.OuterHalf M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

private theorem block_pullback (p : StarGroup) (i : Fin 759) :
    ∃ k : Fin 759, ∀ x, incident k x ↔ incident i (p.val x) := by
  let u := starGroupEquivM24 p
  have hb : (u⁻¹).val • m24BlockAt i ∈ m24Blocks := by
    have h := (mem_M24_iff (u⁻¹).val).mp (u⁻¹).property
    change (u⁻¹).val • m24BlockAt i ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← h]
    exact Set.smul_mem_smul_set (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hb
  refine ⟨k,fun x => ?_⟩
  change StarOrderCertificate.relabel x ∈ m24BlockAt k ↔ _
  rw [hk]
  change StarOrderCertificate.relabel x ∈ u.val⁻¹ • m24BlockAt i ↔ _
  rw [Finset.mem_inv_smul_finset_iff]
  have he : u.val (StarOrderCertificate.relabel x) =
      StarOrderCertificate.relabel (p.val x) := by
    rw [show u = starGroupEquivM24 p from rfl,starGroupEquivM24_apply]
    simp
  change u.val (StarOrderCertificate.relabel x) ∈ m24BlockAt i ↔
    StarOrderCertificate.relabel (p.val x) ∈ m24BlockAt i
  rw [he]

private theorem stable_twins_all (i : Fin 759) (hi : Stable i) :
    incident i 0 ↔ incident i 11 := by
  obtain ⟨j,rfl⟩ := stable_exhaustive i hi
  exact stable_twins j

private theorem centralizer_tetrad_label (p : StarGroup) (hp : Commute p freePair) :
    Nat.xor (pairLabel (p.val 0) (p.val 1))
      (pairLabel (p.val 11) (p.val 12)) = 818 := by
  have hc (x : Fin 24) : p.val (freePair.val x) = freePair.val (p.val x) :=
    congrArg (fun g : StarGroup => g.val x) hp.eq
  have hprof (j : Fin 15) : incident (stableIndex j) (p.val 0) ↔
      incident (stableIndex j) (p.val 11) := by
    obtain ⟨k,hk⟩ := block_pullback p (stableIndex j)
    have hs : Stable k := by
      intro x
      rw [hk,hk,hc]
      exact stable_indices j _
    exact (hk 0).symm.trans ((stable_twins_all k hs).trans (hk 11))
  have he := twin_label (p.val 0) (p.val 11) (p.val.injective.ne (by decide))
    (by rw [← hc]; exact p.val.injective.ne (by decide)) hprof
  rw [← hc,← hc] at he
  exact he

/-- Every lift of the quotient centralizer fixes the distinguished tetrad. -/
theorem tetrad_centralizes (c : M) (hc : Commute (starHom c) freePair) :
    Commute c (kernelValue 818) := by
  have ht : kernelValue 818 = kernelValue (pairLabel 0 1) * kernelValue (pairLabel 11 12) := by
    rw [← kernelValue_xor]
    rfl
  have he : c * kernelValue 818 * c⁻¹ = kernelValue 818 := by
    change (MulAut.conj c).toMonoidHom _ = _
    rw [ht,map_mul]
    change (c * _ * c⁻¹) * (c * _ * c⁻¹) = _
    rw [show c * kernelValue (pairLabel 0 1) * c⁻¹ =
      kernelValue (pairLabel ((starHom c).val 0) ((starHom c).val 1)) from
        congrArg Subtype.val (starHom_pair c 0 1),
      show c * kernelValue (pairLabel 11 12) * c⁻¹ =
      kernelValue (pairLabel ((starHom c).val 11) ((starHom c).val 12)) from
        congrArg Subtype.val (starHom_pair c 11 12),← kernelValue_xor,
      centralizer_tetrad_label _ hc,← ht]
  exact mul_inv_eq_iff_eq_mul.mp he

private theorem involution_fixed_twins (p : StarGroup) (hp2 : p ^ 2 = 1)
    (hp : Commute p freePair) : p.val 0 = 0 ↔ p.val 11 = 11 := by
  by_cases hp1 : p = 1
  · simp [hp1]
  have ho : orderOf (starGroupEquivM24 p) = 2 :=
    (starGroupEquivM24.orderOf_eq p).trans (orderOf_eq_prime hp2 hp1)
  have fixed_iff (x : Fin 24) :
      StarOrderCertificate.relabel x ∈ M24ChapterHStabilizers.fixedPoints (starGroupEquivM24 p) ↔
      p.val x = x := by
    rw [M24ChapterHStabilizers.mem_fixedPoints]
    change (starGroupEquivM24 p).val (StarOrderCertificate.relabel x) = _ ↔ _
    rw [starGroupEquivM24_apply]
    change StarOrderCertificate.relabel (p.val
      (StarOrderCertificate.relabel.symm (StarOrderCertificate.relabel x))) = _ ↔ _
    rw [Equiv.symm_apply_apply]
    exact StarOrderCertificate.relabel.injective.eq_iff
  rcases M24InvolutionCentralizers.involution_classes (starGroupEquivM24 p) ho with h | h
  · obtain ⟨k,_,hk⟩ := Finset.mem_image.mp (M24ChapterHStabilizers.class2A_fixed_octad h)
    have hf (x : Fin 24) : incident k x ↔ p.val x = x := by
      change StarOrderCertificate.relabel x ∈ m24BlockAt k ↔ _
      rw [hk]
      exact fixed_iff x
    have hs : Stable k := by
      intro x
      rw [hf,hf]
      have hc : p.val (freePair.val x) = freePair.val (p.val x) :=
        congrArg (fun a : StarGroup => a.val x) hp.eq
      rw [hc]
      exact freePair.val.injective.eq_iff
    exact (hf 0).symm.trans ((stable_twins_all k hs).trans (hf 11))
  · have he := M24ChapterHStabilizers.class2B_fixed_empty h
    have hn (x : Fin 24) : p.val x ≠ x := by
      intro hfix
      have hm := (fixed_iff x).mpr hfix
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    exact iff_of_false (hn 0) (hn 11)

private theorem pair_endpoints : ∀ a b : Fin 24,
    pairLabel a b = 1 → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide +kernel
private theorem companion_endpoints : ∀ a b : Fin 24,
    pairLabel a b = 819 → (a = 11 ∧ b = 12) ∨ (a = 12 ∧ b = 11) := by decide +kernel

private theorem pair_characters (w : M) (hw : w ^ 2 = 1)
    (hq : Commute (starHom w) freePair)
    (hseed : Commute w (kernelValue 1)) :
    InnerRelated (kernelValue 1 : Model) w ↔ InnerRelated (kernelValue 819 : Model) w := by
  have hcomp : Commute w (kernelValue 819) := by
    have he : kernelValue 819 = kernelValue 1 * kernelValue 818 := by
      rw [← kernelValue_xor]
      rfl
    rw [he]
    exact hseed.mul_right (tetrad_centralizes w hq)
  have h0 : pairLabel ((starHom w).val 0) ((starHom w).val 1) = 1 := by
    have he := congrArg Subtype.val (starHom_pair w 0 1)
    change w * kernelValue 1 * w⁻¹ = _ at he
    rw [hseed.eq,mul_inv_cancel_right] at he
    exact kernelValue_injective (pairLabel_lt _ _) (by decide) he.symm
  have h11 : pairLabel ((starHom w).val 11) ((starHom w).val 12) = 819 := by
    have he := congrArg Subtype.val (starHom_pair w 11 12)
    change w * kernelValue 819 * w⁻¹ = _ at he
    rw [hcomp.eq,mul_inv_cancel_right] at he
    exact kernelValue_injective (pairLabel_lt _ _) (by decide) he.symm
  have hf := involution_fixed_twins (starHom w) (by rw [← map_pow,hw,map_one]) hq
  rcases pair_endpoints _ _ h0 with ha | ha
  · rcases companion_endpoints _ _ h11 with hb | hb
    · exact iff_of_true (inner_of_star_fixed w 0 1 (by decide) ha.1 ha.2)
        (inner_of_star_fixed w 11 12 (by decide) hb.1 hb.2)
    · exact (show (12 : Fin 24) ≠ 11 from by decide) (hb.1.symm.trans (hf.mp ha.1)) |>.elim
  · rcases companion_endpoints _ _ h11 with hb | hb
    · exact (show (1 : Fin 24) ≠ 0 from by decide) (ha.1.symm.trans (hf.mpr hb.1)) |>.elim
    · exact iff_of_false (LinearFive.Geometry.not_inner_of_star_swap w 0 1 (by decide) ha.1 ha.2)
        (LinearFive.Geometry.not_inner_of_star_swap w 11 12 (by decide) hb.1 hb.2)

private theorem centralizer_image_commutes (X : Subgroup Model)
    (hq : freePair ∈ (X.subgroupOf M).map starHom)
    (c : M) (hc : (c : Model) ∈ centralizer (X : Set Model)) :
    Commute (starHom c) freePair := by
  obtain ⟨x,hx,he⟩ := hq
  have hcx : Commute c x := Subtype.ext (hc x hx).symm
  exact he ▸ hcx.map starHom

/-- The full centralizer fixes the native tetrad. The sole quotient premise
is occurrence of the literal fixed-point-free pair. -/
theorem centralizer_le_tetrad_centralizer (X : Subgroup Model)
    (hq : freePair ∈ (X.subgroupOf M).map starHom)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralizer (X : Set Model) ≤ centralizer ({NonsingularC.centralInvolution} : Set Model) := by
  intro c hc
  let c0 : M := ⟨c,hCM hc⟩
  exact mem_centralizer_singleton_iff.mpr (congrArg (fun x : M => (x : Model))
    (tetrad_centralizes c0 (centralizer_image_commutes X hq c0 hc)).eq)

/-- The fixed-point-free pair supplies a nonzero element of the radical of
the canonical central omega, with no restriction on the rest of the image. -/
theorem centralInvolution_mem_radical (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (hq : freePair ∈ (X.subgroupOf M).map starHom) :
    NonsingularC.centralInvolution ∈ NonsingularC.zeroWitness X := by
  have hCM : centralizer (X : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  have hcomm (c : Model) (hc : c ∈ centralizer (X : Set Model)) :
      c * NonsingularC.centralInvolution = NonsingularC.centralInvolution * c :=
    mem_centralizer_singleton_iff.mp (centralizer_le_tetrad_centralizer X hq hCM hc)
  have ht : NonsingularC.centralInvolution ∈ omegaCenterIn (centralizer (X : Set Model)) :=
    (mem_omegaCenterIn_iff _ _).mpr
      ⟨fun x hx => hcomm x (X.le_centralizer hx),hcomm,
        NonsingularC.centralInvolution_order ▸ pow_orderOf_eq_one _⟩
  refine ⟨ht,?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1,outerValue_one_right]
  have hwC : w ∈ centralizer (X : Set Model) := map_subtype_le _ hw
  let w0 : M := ⟨w,hCM hwC⟩
  have hw2 : orderOf w = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw) hw1
  have hsw : Commute w0 (kernelValue 1) := by
    have he : kernelValue 1 = seed := maskValue_one _ _
    rw [he]
    apply Subtype.ext
    exact (hwC seed hs).symm
  have hi := pair_characters w0 (Subtype.ext (hw2 ▸ pow_orderOf_eq_one w))
    (centralizer_image_commutes X hq w0 hwC) hsw
  have hp : NonsingularC.centralInvolution = (kernelValue 1 : Model) * (kernelValue 819 : Model) := by
    change (kernelValue 818 : Model) = ((kernelValue 1 * kernelValue 819 : M) : Model)
    rw [← kernelValue_xor]
    rfl
  have hc0 : Commute w (kernelValue 1 : Model) :=
    congrArg (fun x : M => (x : Model)) hsw.eq
  have hc1 : Commute w (kernelValue 819 : Model) := by
    have he : kernelValue 819 = kernelValue 1 * kernelValue 818 := by rw [← kernelValue_xor]; rfl
    have hc : Commute w0 (kernelValue 819) := by
      rw [he]
      exact hsw.mul_right (tetrad_centralizes w0 (centralizer_image_commutes X hq w0 hwC))
    exact congrArg (fun x : M => (x : Model)) hc.eq
  have ho0 : orderOf (kernelValue 1 : Model) = 2 := pair_order 0 1 (by decide)
  have ho1 : orderOf (kernelValue 819 : Model) = 2 := pair_order 11 12 (by decide)
  have hie : InnerRelated w (kernelValue 1 : Model) ↔ InnerRelated w (kernelValue 819 : Model) :=
    (innerRelated_symm _ _ ho0 hw2 hc0.symm).symm.trans
      (hi.trans (innerRelated_symm _ _ ho1 hw2 hc1.symm))
  have hv : outerValue w (kernelValue 1 : Model) = outerValue w (kernelValue 819 : Model) := by
    simp only [outerValue,hw1,false_or]
    rw [hie]
  have hz : outerValue w NonsingularC.centralInvolution = 0 := by
    rw [hp,outerValue_mul_right w hw2 _ _ hc0 hc1,hv,← two_mul]
    rw [show (2 : ZMod 2) = 0 from rfl,zero_mul]
  have hwt : Commute w NonsingularC.centralInvolution :=
    (mem_omegaCenterIn_iff _ _).mp ht |>.2.1 w hwC
  exact (outerValue_eq_zero_iff _ _ NonsingularC.centralInvolution_ne_one).mpr
    ((innerRelated_symm _ _ hw2 NonsingularC.centralInvolution_order hwt).mp
      ((outerValue_eq_zero_iff _ _ hw1).mp hz))

/-- The ABB(3) quotient branch has a NONTRIVIAL zero-form subgroup normalized
by the whole original normalizer. No nondegeneracy exclusion is assumed. -/
theorem source_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (hq : freePair ∈ (X.subgroupOf M).map starHom) :
    NonsingularC.zeroWitness X ≠ ⊥ ∧
      intrinsicElementaryForm (NonsingularC.zeroWitness X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (NonsingularC.zeroWitness X : Set Model) := by
  have ht := centralInvolution_mem_radical X hs hq
  exact ⟨fun he => NonsingularC.centralInvolution_ne_one (mem_bot.mp (he ▸ ht)),
    NonsingularC.zeroWitness_form X,NonsingularC.zeroWitness_normalizer X⟩


end Janko4.LocalStructure.ElementaryNormalizerCover.ABB
