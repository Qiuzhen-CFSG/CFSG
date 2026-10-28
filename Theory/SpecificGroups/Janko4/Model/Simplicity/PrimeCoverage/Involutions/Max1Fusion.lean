module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideReduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.InvolutionFibers
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideWordFusion

/-!
# Assembly of involution fusion in the concrete local subgroup

The elementary abelian local kernel and its complementing cases are kept
separate. Inside the kernel it suffices to conjugate to u=(xy)^14 or
u*(x⁻¹*u*x); `Max1Fusion.Seeds` proves their ambient fusion by checked
odd-product certificates. `Max1Fusion.KernelOrbits` certifies the kernel orbits.
Outside the kernel, `QuotientInvolutions` and `InvolutionFibers` give coverage
by ten concrete words, using `OutsideReduction` to lift quotient conjugators.
`OutsideWordFusion` fuses those words by checked odd-product identities.
The final theorem `max1InvolutionFusion` combines these certificates with no
additional hypotheses beyond the original two generator identities.

The local generators are the literal ATLAS `J4G1-max1W1` outputs documented
in `Cardinality.Subgroup`. All final conjugators belong to `Model`.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

public section
namespace Janko4.Simplicity
open Cardinality Max1Fusion
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localX localY
  localKernelSeed localKernel

/-- Local kernel conjugacy and outside fusion together give the precise
maximal-subgroup fusion certificate. Neither remaining premise is asserted. -/
theorem max1InvolutionFusion_of_kernel_orbits_of_outside
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hkernel : ∀ z : max1Subgroup hA hB, z ∈ localKernel hA hB →
      orderOf z = 2 → ∃ g : max1Subgroup hA hB,
        localKernelSeed hA hB = g * z * g⁻¹ ∨
        kernelPair hA hB = g * z * g⁻¹)
    (houtside : ∀ z : max1Subgroup hA hB, z ∉ localKernel hA hB →
      orderOf z = 2 → Fuses hA hB (z : Model)) :
    Max1InvolutionFusion hA hB := by
  intro z hz ho
  let zl : max1Subgroup hA hB := ⟨z, hz⟩
  have hol : orderOf zl = 2 :=
    (orderOf_injective (max1Subgroup hA hB).subtype
      (max1Subgroup hA hB).subtype_injective zl).symm.trans ho
  by_cases hk : zl ∈ localKernel hA hB
  · obtain ⟨g, hg | hg⟩ := hkernel zl hk hol
    · obtain ⟨k, hr⟩ := seed_fuses_second hA hB
      have he := congrArg (fun x : max1Subgroup hA hB => (x : Model)) hg
      change (localKernelSeed hA hB : Model) = (g : Model) * z * (g : Model)⁻¹ at he
      rw [he] at hr
      exact ⟨k * (g : Model), Or.inr (by
        simpa only [mul_inv_rev, mul_assoc] using hr)⟩
    · obtain ⟨k, hr⟩ := pair_fuses_first hA hB
      have he := congrArg (fun x : max1Subgroup hA hB => (x : Model)) hg
      change (kernelPair hA hB : Model) = (g : Model) * z * (g : Model)⁻¹ at he
      rw [he] at hr
      exact ⟨k * (g : Model), Or.inl (by
        simpa only [mul_inv_rev, mul_assoc] using hr)⟩
  · exact houtside zl hk hol

/-- Three independent certificates finish the local fusion problem: the two
kernel orbits, coverage by the ten outside words, and fusion of those words. -/
theorem max1InvolutionFusion_of_three_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hkernel : ∀ z : max1Subgroup hA hB, z ∈ localKernel hA hB →
      orderOf z = 2 → ∃ g : max1Subgroup hA hB,
        localKernelSeed hA hB = g * z * g⁻¹ ∨
        kernelPair hA hB = g * z * g⁻¹)
    (houtside : ∀ z : max1Subgroup hA hB, z ∉ localKernel hA hB →
      orderOf z = 2 → ∃ (i : Fin 10) (g : max1Subgroup hA hB),
        outsideRepresentative hA hB i = g * z * g⁻¹)
    (hreps : ∀ i : Fin 10, Fuses hA hB (outsideRepresentative hA hB i : Model)) :
    Max1InvolutionFusion hA hB := by
  apply max1InvolutionFusion_of_kernel_orbits_of_outside hA hB hkernel
  intro z hz ho
  obtain ⟨i, g, hg⟩ := houtside z hz ho
  exact fuses_of_conjugate hA hB (g : Model)
    (congrArg (fun x : max1Subgroup hA hB => (x : Model)) hg) (hreps i)

/-- The complete kernel branch, using the certified orbit tree and seed fusion. -/
theorem max1_kernel_involutions_fuse
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (z : max1Subgroup hA hB) (hz : z ∈ localKernel hA hB) (ho : orderOf z = 2) :
    Fuses hA hB (z : Model) := by
  obtain ⟨g, hg | hg⟩ := kernel_involution_orbits hA hB z hz ho
  · obtain ⟨k, hk⟩ := seed_fuses_second hA hB
    exact fuses_of_conjugate hA hB (g : Model)
      (congrArg (fun w : max1Subgroup hA hB => (w : Model)) hg) ⟨k, Or.inr hk⟩
  · obtain ⟨k, hk⟩ := pair_fuses_first hA hB
    exact fuses_of_conjugate hA hB (g : Model)
      (congrArg (fun w : max1Subgroup hA hB => (w : Model)) hg) ⟨k, Or.inl hk⟩

/-- Only the outside-kernel branch remains after the kernel certificates. -/
theorem max1InvolutionFusion_of_outside
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (houtside : ∀ z : max1Subgroup hA hB, z ∉ localKernel hA hB →
      orderOf z = 2 → Fuses hA hB (z : Model)) :
    Max1InvolutionFusion hA hB :=
  max1InvolutionFusion_of_kernel_orbits_of_outside hA hB
    (kernel_involution_orbits hA hB) houtside

/-- Outside coverage and fusion of the ten words finish the task. The two
remaining certificates are hypotheses, not claims of this theorem. -/
theorem max1InvolutionFusion_of_outside_certificates
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (houtside : ∀ z : max1Subgroup hA hB, z ∉ localKernel hA hB →
      orderOf z = 2 → ∃ (i : Fin 10) (g : max1Subgroup hA hB),
        outsideRepresentative hA hB i = g * z * g⁻¹)
    (hreps : ∀ i : Fin 10, Fuses hA hB (outsideRepresentative hA hB i : Model)) :
    Max1InvolutionFusion hA hB :=
  max1InvolutionFusion_of_three_certificates hA hB
    (kernel_involution_orbits hA hB) houtside hreps

/-- Every involution of the concrete ATLAS local subgroup is conjugate inside
`Model` to `a` or `(ababb)^5`. All kernel, quotient, fiber, and word-fusion
certificates are discharged. -/
theorem max1InvolutionFusion
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Max1InvolutionFusion hA hB :=
  max1InvolutionFusion_of_outside_certificates hA hB
    (outside_coverage_of_quotient_and_fibers hA hB
      (quotient_involution_coverage hA hB) (involution_fibers hA hB))
    (outsideRepresentative_fuses hA hB)

end Janko4.Simplicity
