module

public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.CentralizerGeometry
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.SectionAction

/-!
# Recovering the involution from its native fixed four-space

The earlier faithful common-center action puts the octad fixed line inside
Vz. A pointwise fixer of Vz therefore stabilizes the octad. Conjugating z by
such a fixer gives another kernel actor with the same fixed hyperplane;
binary line-map rigidity identifies it with z. Thus the ambient pointwise
centralizer of Vz lies in C_M(z), and its relative kernel is the same subgroup.

The applications below connect this containment to the published transvection
alternative and reduce the ambient W-kernel and every subgroup fixed-rank
calculation to the two action kernels of a supplied elementary supplement.
Those supplement action hypotheses are explicit, unproved inputs here;
this module does not claim all of H.16.2(5--8). The SectionAction owner retains
their discharge. The parent centralizer-geometry owner constructs the supplied
supplement independently, and the code-local owner supplies the earlier flag.

Source: Aschbacher--Smith, H.16.2, printed pp.402--403.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.ChapterH.Section13To16


private theorem octad_line_finrank (O : Octad) :
    Module.finrank (ZMod 2) (fixedSpace MathieuCode.codeRepresentation (octadKernel O)) = 1 := by
  rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
  exact MathieuCode.octad_fixedSpace_finrank O

/-- A nonidentity center actor moves some vector onto the octad fixed line. -/
theorem codeOctad_line_le_involutionFixed (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    fixedSpace MathieuCode.codeRepresentation (octadKernel O) ≤ codeOctadInvolutionFixed O z := by
  obtain ⟨v, hv, hmove⟩ : ∃ v ∈ codeOctadMoved O, MathieuCode.codeRepresentation z v ≠ v := by
    by_contra hn
    push Not at hn
    have hm : z ∈ subspaceKernel MathieuCode.codeRepresentation (codeOctadMoved O)
        (octadKernel O) := ⟨hz, hn⟩
    exact hne (by simpa only [h.faithful, Subgroup.mem_bot] using hm)
  have hLW : fixedSpace MathieuCode.codeRepresentation (octadKernel O) ≤ codeOctadMoved O := by
    rw [eq_span_singleton_of_mem_of_finrank_eq_one (octad_line_finrank O)
      (h.displacement z hz v hv) (sub_ne_zero.mpr hmove)]
    apply Submodule.span_le.mpr
    exact Set.singleton_subset_iff.mpr (Submodule.subset_span
      ⟨z, hz, v, Submodule.mem_top, rfl⟩)
  exact le_inf hLW (fixedSpace_antitone _ (Subgroup.zpowers_le.mpr hz))

/-- Pointwise fixation of Vz recovers the native octad. -/
theorem codeOctadInvolutionCentralizer_le_stabilizer (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    codeOctadInvolutionCentralizer O z ≤ octadStabilizer O := by
  intro g hg
  apply (MathieuCode.SectionAction.octadVector_fixed_iff O g).mp
  apply hg.2
  apply codeOctad_line_le_involutionFixed O h z hz hne
  rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
  exact MathieuCode.octadVector_fixed O

/-- The ambient pointwise centralizer of Vz centralizes the actual involution z. -/
theorem codeOctadInvolutionCentralizer_le_centralizer (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    codeOctadInvolutionCentralizer O z ≤ Subgroup.centralizer ({z} : Set M24) := by
  intro g hg
  have hn : g ∈ Subgroup.normalizer (octadKernel O) := by
    rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
    exact MathieuCode.octad_stabilizer_le_normalizer_pointwiseKernel O
      (codeOctadInvolutionCentralizer_le_stabilizer O h z hz hne hg)
  have ha : g * z * g⁻¹ ∈ octadKernel O := (Subgroup.mem_normalizer_iff.mp hn z).mp hz
  have ha1 : g * z * g⁻¹ ≠ 1 := by
    intro he
    apply hne
    have he' := congrArg (fun x => g⁻¹ * x * g) he
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
      mul_one, inv_mul_cancel] using he'
  have he : z = g * z * g⁻¹ := by
    apply binary_center_action_eq_of_fixed_le MathieuCode.codeRepresentation (octadKernel O)
      (codeOctadMoved O) (fixedSpace MathieuCode.codeRepresentation (octadKernel O))
      (octad_line_finrank O) h.displacement h.faithful z (g * z * g⁻¹) hz ha ha1
    intro v hv
    refine ⟨hv.1, (mem_fixedSpace_zpowers_iff _ _ v).mpr ?_⟩
    have hgv : MathieuCode.codeRepresentation g v = v := hg.2 v hv
    have hgi : MathieuCode.codeRepresentation g⁻¹ v = v := by
      rw [← hgv]
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply]
      exact hgv.symm
    simp only [map_mul, Module.End.mul_apply]
    rw [hgi, (mem_fixedSpace_zpowers_iff _ _ v).mp hv.2, hgv]
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (eq_mul_inv_iff_mul_eq.mp he).symm


/-- The source D can now be computed inside C_M(z), with no ambient-fixer premise. -/
theorem codeOctadInvolutionCentralizer_eq_relative (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    codeOctadInvolutionCentralizer O z =
      subspaceKernel MathieuCode.codeRepresentation (codeOctadInvolutionFixed O z)
        (Subgroup.centralizer ({z} : Set M24)) := by
  apply le_antisymm
  · intro g hg
    exact ⟨codeOctadInvolutionCentralizer_le_centralizer O h z hz hne hg, hg.2⟩
  · intro g hg
    exact ⟨Subgroup.mem_top _, hg.2⟩

/-- The pointwise fixer of W is already in the element centralizer. -/
theorem codeInvolutionFixed_kernel_le_centralizer (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    subspaceKernel MathieuCode.codeRepresentation (codeInvolutionFixed z) ⊤ ≤
      Subgroup.centralizer ({z} : Set M24) := by
  intro g hg
  exact codeOctadInvolutionCentralizer_le_centralizer O h z hz hne
    ⟨hg.1, fun v hv => hg.2 v hv.2⟩

/-- Application to the published transvection alternative: its first branch is
exactly the kernel inside C_M(z). The remaining two relative-kernel calculations
are independent source obligations. -/
theorem codeInvolution_transvection_relative_alternative (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) (g : M24)
    (hg : g ∈ Subgroup.centralizer ({z} : Set M24))
    (ht : fixedCodim
      (stabilizerRepresentation MathieuCode.codeRepresentation (codeInvolutionFixed z))
      (Subgroup.zpowers ⟨g, codeInvolutionFixed_stable z hg⟩) = 1) :
    g ∈ subspaceKernel MathieuCode.codeRepresentation (codeOctadInvolutionFixed O z)
        (Subgroup.centralizer ({z} : Set M24)) ∨
      ∀ v ∈ codeInvolutionFixed z,
        MathieuCode.codeRepresentation g v - v ∈ codeOctadInvolutionFixed O z := by
  have ha := codeInvolution_transvection_alternative O z hz hne g hg ht
  rwa [codeOctadInvolutionCentralizer_eq_relative O h z hz hne] at ha

/-- Once the two native supplement action calculations are available, they
supply the published common-center rank consumer for every subgroup B containing z.
The hypotheses concern U itself; the cyclic kernel for each B is derived here.
The SectionAction assembly owner must still discharge these two action premises. -/
theorem codeInvolution_fixed_rank_of_supplement_action (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (s : MathieuCode.OctadInvolutionSupplement O z)
    (hd : ∀ u ∈ s.carrier, ∀ v ∈ codeInvolutionFixed z,
      MathieuCode.codeRepresentation u v - v ∈
        fixedSpace MathieuCode.codeRepresentation (octadKernel O))
    (hk : subspaceKernel MathieuCode.codeRepresentation (codeInvolutionFixed z) s.carrier =
      Subgroup.zpowers z)
    (B : Subgroup M24) (hBU : B ≤ s.carrier) (hzB : z ∈ B) :
    Module.finrank (ZMod 2) (fixedSpace MathieuCode.codeRepresentation B) = 8 - rank B := by
  let := s.elementary
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (congrArg (fun u : s.carrier => (u : M24)) (mul_comm (⟨x.val, hBU x.property⟩ : s.carrier)
        ⟨y.val, hBU y.property⟩))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val (hBU x.property))) }
  have ho : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z (hBU hzB)) hne
  apply codeInvolution_fixed_rank_of_common_center O z hz ho B hzB
    (hBU.trans s.le_centralizer) (fun b hb => hd b (hBU hb))
  apply le_antisymm
  · intro b hb
    rw [← hk]
    exact ⟨hBU hb.1, hb.2⟩
  · intro b hb
    exact ⟨Subgroup.zpowers_le.mpr hzB hb, fun v hv => hv ⟨b, hb⟩⟩

/-- The two relative supplement kernels imply the full ambient pointwise
centralizer assertion in H.16.2(5). Their native action calculations remain
explicit inputs, to be discharged by the SectionAction assembly. -/
theorem codeInvolution_ambient_kernel_of_supplement_kernels
    (O : Octad) (h : CodeOctadCenterAction O) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (s : MathieuCode.OctadInvolutionSupplement O z)
    (hVz : subspaceKernel MathieuCode.codeRepresentation (codeOctadInvolutionFixed O z)
      (Subgroup.centralizer ({z} : Set M24)) = s.carrier)
    (hW : subspaceKernel MathieuCode.codeRepresentation (codeInvolutionFixed z) s.carrier =
      Subgroup.zpowers z) :
    subspaceKernel MathieuCode.codeRepresentation (codeInvolutionFixed z) ⊤ =
      Subgroup.zpowers z := by
  apply le_antisymm
  · intro g hg
    have hD : g ∈ codeOctadInvolutionCentralizer O z :=
      ⟨Subgroup.mem_top _, fun v hv => hg.2 v hv.2⟩
    have hU : g ∈ s.carrier := by
      rw [← hVz, ← codeOctadInvolutionCentralizer_eq_relative O h z hz hne]
      exact hD
    have hk : g ∈ subspaceKernel MathieuCode.codeRepresentation (codeInvolutionFixed z)
        s.carrier := ⟨hU, hg.2⟩
    simpa only [hW] using hk
  · intro g hg
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨g, hg⟩⟩

end CFSG.Quasithin.ChapterH.Section13To16
