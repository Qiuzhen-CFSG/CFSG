module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.SecondPairs
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Assembly
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits

/-!
# Second-class pairs in the elementary centralizer kernel

The actual max1 kernel has two nonidentity local orbits. Ambient class
separation eliminates its first-class orbit for a second-class involution.
A conjugator in max1 then carries it to the marked seed and preserves the
whole elementary kernel. This proves both full-residual memberships, and
applies to the intrinsic two-core of the full seed centralizer.

Source: Kleidman--Wilson (1988), pp.485--487, the elementary 2^11 local
and the four-group comparisons used in Corollary 1.1.4. This is the kernel
branch only; the other second-centralizer fibers remain separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.InvolutionCentralizers.Second
open Janko4.Cardinality Janko4.Simplicity.Max1Fusion
open Janko4.Cardinality.LocalInvolutionCensus
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  max1Subgroup localKernel localKernelSeed

/-- Ambient second-class fusion inside the elementary kernel is already
conjugacy within the actual max1 subgroup. -/
theorem second_kernel_isConj_seed (u : InvolutionCentralizers.Second.Local)
    (hu : u ∈ max1Kernel) (hb : IsConj (seed : Model) (u : Model)) :
    IsConj u seed := by
  have hne : u ≠ 1 := by
    intro he
    have he' : (u : Model) = 1 := congrArg Subtype.val he
    have hz := isConj_one_left.mp (he' ▸ hb)
    have ho := seed_order
    rw [hz, orderOf_one] at ho
    omega
  obtain ⟨g, hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four u hu hne
  · exact isConj_iff.mpr ⟨g, hg.symm⟩
  · have hup : IsConj (u : Model)
        (kernelPair matrixA_mul_self matrixB_pow_four : Model) := by
      exact isConj_iff.mpr ⟨(g : Model), congrArg Subtype.val hg.symm⟩
    obtain ⟨k, hk⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
    have hpa : IsConj (kernelPair matrixA_mul_self matrixB_pow_four : Model)
        Janko4.a := isConj_iff.mpr ⟨k, hk.symm⟩
    exact (not_isConj_z_t (hb.trans (hup.trans hpa)).symm).elim

/-- Both full-centralizer residual memberships for a second-class kernel pair. -/
theorem second_kernel_pair_inner (u : InvolutionCentralizers.Second.Local)
    (hu : u ∈ max1Kernel) (hb : IsConj (seed : Model) (u : Model)) :
    InnerRelated (seed : Model) (u : Model) ∧
      InnerRelated (u : Model) (seed : Model) := by
  refine ⟨innerRelated_second_kernel u hu, ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (second_kernel_isConj_seed u hu hb)
  have hs : g * seed * g⁻¹ ∈ max1Kernel :=
    (inferInstance : max1Kernel.Normal).conj_mem _ (localKernelSeed_mem _ _) g
  apply (innerRelated_equiv (MulAut.conj (g : Model)) _ _).mp
  have he : (MulAut.conj (g : Model)) (u : Model) = (seed : Model) :=
    congrArg Subtype.val hg
  rw [he]
  exact innerRelated_second_kernel (g * seed * g⁻¹) hs

/-- The intrinsic full two-core, with its literal ambient inclusion, supplies
the kernel branch of second-class symmetry. -/
theorem second_core_pair_inner (y : Model)
    (hy : y ∈ (pCore 2 ambientCentralizer).map ambientCentralizer.subtype)
    (hb : IsConj (seed : Model) y) :
    InnerRelated (seed : Model) y ∧ InnerRelated y (seed : Model) := by
  rw [ambient_twoCore_eq_kernel, ambientKernel_eq_map, map_map] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  change InnerRelated (seed : Model) (ambientEquivLocal.symm k : Model) ∧
    InnerRelated (ambientEquivLocal.symm k : Model) (seed : Model)
  rw [ambientEquivLocal_symm_val]
  apply second_kernel_pair_inner k.val hk
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply,
    MulEquiv.coe_toMonoidHom, ambientEquivLocal_symm_val] using hb

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
