module

public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.CentralizerGeometry.SectionAction

/-!
# Native supplement displacement

The commutator of a supplement actor with an octad-kernel actor lies in the
cyclic intersection `⟨z⟩`. Since `z` fixes the involution fixed space, this
commutator calculation makes every supplement displacement on that fixed space
fixed by the octad kernel, hence it lies in the octad fixed line.

Source: Aschbacher--Smith, H.16.2, printed pp.402--403.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.ChapterH.Section13To16

theorem supplement_displacement_into_octad_fixed (O : Octad) (z : M24)
    (hz : z ∈ octadPointwiseKernel O) (hne : z ≠ 1)
    (s : OctadInvolutionSupplement O z)
    (hfix : ∀ u ∈ s.carrier, ∀ v ∈
      subspaceCommutator codeRepresentation ⊤ (octadPointwiseKernel O) ⊓
        fixedSpace codeRepresentation (Subgroup.zpowers z), codeRepresentation u v = v) :
    ∀ u ∈ s.carrier, ∀ w ∈ fixedSpace codeRepresentation (Subgroup.zpowers z),
      codeRepresentation u w - w ∈ fixedSpace codeRepresentation (octadPointwiseKernel O) := by
  let K := octadPointwiseKernel O
  let C := Subgroup.centralizer ({z} : Set M24)
  have hKC : K ≤ C := by
    let := octad_pointwiseKernel_elementary O
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨k, hk⟩ : K) ⟨z, hz⟩))
  have hNK : C ≤ Subgroup.normalizer K :=
    (octad_kernel_centralizer_le_stabilizer O z hz hne).trans
      (octad_stabilizer_le_normalizer_pointwiseKernel O)
  have hNU : C ≤ Subgroup.normalizer s.carrier :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer s.le_centralizer).mp s.normal
  intro u hu w hw k
  let c := k.val⁻¹ * u⁻¹ * k.val * u
  have hcK : c ∈ K := by
    dsimp [c]
    rw [mul_assoc, mul_assoc]
    change k.val⁻¹ * (u⁻¹ * k.val * u) ∈ K
    exact K.mul_mem (K.inv_mem k.property)
      ((Subgroup.mem_normalizer_iff''.mp (hNK (s.le_centralizer hu)) k.val).mp k.property)
  have hcU : c ∈ s.carrier := by
    exact s.carrier.mul_mem
      ((Subgroup.mem_normalizer_iff''.mp (hNU (hKC k.property)) u⁻¹).mp
        (s.carrier.inv_mem hu)) hu
  have hcz : c ∈ Subgroup.zpowers z := by
    rw [← s.intersection]
    exact ⟨hcK, hcU⟩
  have hcomm : codeRepresentation k.val (codeRepresentation u w) =
      codeRepresentation u (codeRepresentation k.val w) := by
    have he : k.val * u = u * k.val * c := by dsimp [c]; group
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]
    have hcfix : codeRepresentation c w = w :=
      hw ⟨c, hcz⟩
    rw [hcfix, map_mul, Module.End.mul_apply]
  have hd : codeRepresentation k.val w - w ∈
      subspaceCommutator codeRepresentation ⊤ K ⊓
        fixedSpace codeRepresentation (Subgroup.zpowers z) := by
    refine ⟨Submodule.subset_span ⟨k.val, k.property, w, Submodule.mem_top, rfl⟩, ?_⟩
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    have hwz := (mem_fixedSpace_zpowers_iff codeRepresentation z w).mp hw
    have hzk := Subgroup.mem_centralizer_singleton_iff.mp (hKC k.property)
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← hzk,
      map_mul, Module.End.mul_apply, hwz]
  have he := hfix u hu _ hd
  rw [map_sub] at he
  change codeRepresentation k.val (codeRepresentation u w - w) = _
  rw [map_sub, hcomm]
  exact sub_eq_sub_iff_sub_eq_sub.mp he
end CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The same displacement statement on the chapter's mapped octad kernel. -/
theorem supplement_displacement
    (O : Octad) (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (s : OctadInvolutionSupplement O z)
    (hfix : ∀ u ∈ s.carrier, ∀ v ∈ codeOctadInvolutionFixed O z,
      MathieuCode.codeRepresentation u v = v) :
    ∀ u ∈ s.carrier, ∀ w ∈ codeInvolutionFixed z,
      MathieuCode.codeRepresentation u w - w ∈
        fixedSpace MathieuCode.codeRepresentation (octadKernel O) := by
  have hz' : z ∈ octadPointwiseKernel O := by
    simpa only [octadKernel, MathieuCode.octad_core_map_eq_pointwise] using hz
  have hfix' : ∀ u ∈ s.carrier, ∀ v ∈
      subspaceCommutator MathieuCode.codeRepresentation ⊤ (octadPointwiseKernel O) ⊓
        fixedSpace MathieuCode.codeRepresentation (Subgroup.zpowers z),
      MathieuCode.codeRepresentation u v = v := by
    intro u hu v hv
    apply hfix u hu v
    refine ⟨?_, hv.2⟩
    simpa only [codeOctadMoved, octadKernel,
      MathieuCode.octad_core_map_eq_pointwise] using hv.1
  have h := supplement_displacement_into_octad_fixed O z hz' hne s hfix'
  intro u hu w hw
  have hw' := h u hu w hw
  simpa only [octadKernel, MathieuCode.octad_core_map_eq_pointwise] using hw'

end CFSG.Quasithin.ChapterH.Section13To16
