module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalQuotients

/-!
# The concrete four-set intersections in the split heptad stabilizer

The proved alternating image and section discharge the hypotheses of the
labelled partition calculation. Thus Ix/U is genuinely S3 × C2, with the
quotient map compatible with inclusion in the heptad quotient. The two-pair
intersection and four-point kernel are U B for the actual cyclic group B
lifted from the source three-cycle. Membership is also expressed as an actual
product of two ambient M23 elements, and C_U(B) is proved trivial.

Source: Aschbacher--Smith, Lemma 5.2.20(2--3), printed pp.656--657.
The partition and generation assertions of 5.2.22 are re-exported from Local.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- The source local quotient, with all image hypotheses discharged. -/
noncomputable def fourPairBinaryQuotientEquiv :
    fourPairStabilizer ⧸ heptadKernelAmbient.subgroupOf fourPairStabilizer ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) :=
  fourPairQuotientS3C2Equiv heptadAction_range

noncomputable def heptadThreeSubgroup : Subgroup M23 :=
  heptadSectionThreeSubgroup AlternatingSection.s

theorem fourTwoPairStabilizer_eq_binary_three :
    fourTwoPairStabilizer = heptadKernelAmbient ⊔ heptadThreeSubgroup :=
  fourTwoPairStabilizer_eq_kernel_sup heptadAction_range AlternatingSection.s
    AlternatingSection.heptadAction_s

theorem fourKernelAmbient_eq_binary_three :
    fourKernelAmbient = heptadKernelAmbient ⊔ heptadThreeSubgroup :=
  fourKernelAmbient_eq_kernel_sup heptadAction_range AlternatingSection.s
    AlternatingSection.heptadAction_s

@[simp] theorem heptadTripleCycle_eq : heptadTripleCycle = AlternatingSection.c := rfl

/-- The specified source generator is the actual ambient lift of (1,2,3). -/
theorem heptadThreeSubgroup_eq_zpowers : heptadThreeSubgroup =
    Subgroup.zpowers (AlternatingSection.s AlternatingSection.c : M23) := rfl

/-- Membership in UB is an actual product, with both factors in M23. -/
theorem mem_fourTwoPairStabilizer_iff_binary_three (g : M23) :
    g ∈ fourTwoPairStabilizer ↔ ∃ u ∈ heptadKernelAmbient,
      ∃ b ∈ heptadThreeSubgroup, g = u * b := by
  constructor
  · intro hg
    let h : heptadStabilizer := ⟨g, fourPairStabilizer_le_heptad hg.1⟩
    have hh := (mem_fourTwoPairStabilizer_iff_labelled heptadAction_range h).mp hg
    rw [heptadEvenFourFixer_eq_zpowers] at hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    let b : heptadStabilizer := AlternatingSection.s heptadTripleCycle ^ n
    have hb : heptadAction b = heptadAction h := by
      dsimp only [b]
      rw [map_zpow, AlternatingSection.heptadAction_s, hn]
    refine ⟨(h * b⁻¹ : heptadStabilizer), ?_, b, ?_, ?_⟩
    · apply (mem_heptadKernelAmbient_iff_action _).mpr
      rw [map_mul, map_inv, hb, mul_inv_cancel]
    · exact Subgroup.mem_zpowers_iff.mpr ⟨n, (map_zpow heptadStabilizer.subtype _ n).symm⟩
    · change g = (g * (b : M23)⁻¹) * (b : M23)
      simp only [inv_mul_cancel_right]
  · rintro ⟨u, hu, b, hb, rfl⟩
    rw [fourTwoPairStabilizer_eq_binary_three]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hb)

/-- On a representative, the quotient identification is exactly the labelled
partition action followed by its S3 and last-pair coordinates. -/
@[simp] theorem fourPairBinaryQuotientEquiv_mk (g : fourPairStabilizer) :
    fourPairBinaryQuotientEquiv (QuotientGroup.mk g) =
      heptadEvenPartitionEquiv (fourPairPartitionAction heptadAction_range g) := rfl

/-- The lifted three-cycle has order three in the actual heptad stabilizer. -/
theorem heptadThreeLift_order : orderOf (AlternatingSection.s AlternatingSection.c) = 3 := by
  rw [orderOf_injective AlternatingSection.s AlternatingSection.s_injective]
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (AlternatingSection.c : Equiv.Perm (Fin 7)) ^ 3 = 1
    decide +kernel
  · intro h
    have h' := congrArg (fun a : alternatingGroup (Fin 7) => (a : Equiv.Perm (Fin 7))) h
    exact (by decide +kernel : (AlternatingSection.c : Equiv.Perm (Fin 7)) ≠ 1) h'

instance heptadThreeSubgroup_isCyclic : IsCyclic heptadThreeSubgroup :=
  heptadSectionThreeSubgroup_isCyclic AlternatingSection.s

/-- B has order three, as a subgroup of the concrete M23. -/
theorem heptadThreeSubgroup_card : Nat.card heptadThreeSubgroup = 3 := by
  rw [heptadThreeSubgroup_eq_zpowers, Nat.card_zpowers]
  exact (orderOf_injective heptadStabilizer.subtype Subtype.val_injective _).trans
    heptadThreeLift_order

/-- The centralizer C_U(B) is trivial, with both subgroups embedded in M23. -/
theorem heptadKernelAmbient_inf_centralizer_three :
    heptadKernelAmbient ⊓ Subgroup.centralizer (heptadThreeSubgroup : Set M23) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro g ⟨hg, hc⟩
  obtain ⟨u, hu, rfl⟩ := hg
  have hc' := (Subgroup.mem_centralizer_iff.mp hc)
    (AlternatingSection.s AlternatingSection.c : M23)
    (show (AlternatingSection.s AlternatingSection.c : M23) ∈ heptadThreeSubgroup from
      Subgroup.mem_zpowers _)
  have hu1 : (⟨u, hu⟩ : heptadKernel) = 1 := by
    apply (heptadConjugation_cycle_fixed_iff _).mp
    apply Subtype.ext
    rw [heptadConjugation_coe]
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Subtype.ext hc'
  have h := congrArg (fun v : heptadKernel => ((v : heptadStabilizer) : M23)) hu1
  exact h

/-- Inclusion into the ambient heptad quotient is respected by the S3 × C2
identification, through its inverse partition coordinates. -/
theorem fourPairBinaryQuotientEquiv_ambient
    (q : fourPairStabilizer ⧸ heptadKernelAmbient.subgroupOf fourPairStabilizer) :
    (heptadEvenPartitionEquiv.symm (fourPairBinaryQuotientEquiv q) : Equiv.Perm (Fin 7)) =
      QuotientGroup.kerLift heptadAction (fourPairQuotientHeptadMap q) := by
  change (heptadEvenPartitionEquiv.symm
    (heptadEvenPartitionEquiv (fourPairQuotientPartitionEquiv heptadAction_range q)) :
      Equiv.Perm (Fin 7)) = _
  rw [heptadEvenPartitionEquiv.symm_apply_apply]
  exact fourPairQuotientPartitionEquiv_ambient heptadAction_range q

end Sporadic.Mathieu.M23Geometry
