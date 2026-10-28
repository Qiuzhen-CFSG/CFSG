module

public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.Spaces
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# The involution fixed flag on the native code

For a Sylow subgroup stabilizing the octad, its central involution lies in
the intrinsic octad kernel. The literal code fixed space has dimension seven,
its centralizer stabilizes the octad, and its two-core contains the octad kernel.
On the exact earlier H.16.2(1--2) boundary (the five-dimensional moved space,
faithfulness there, and displacement into the octad fixed line), Vz has dimension
four. No centralizer conclusion is assumed in that boundary.

The transvection alternative uses the actual nested fixed spaces: a transvection
on C_V(z) fixes Vz or is trivial on C_V(z)/Vz. The group-theoretic containment
of these two kernels, the elementary supplement, and the full source clauses
(5--8) remain separate obligations. Thus the conditional assertions below are
not labeled unconditional proofs of H.16.2.

Source: Aschbacher--Smith, H.16.2 and its proof, printed pp.402--403.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.Section13To16

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender

/-- Precisely the portions of H.16.2(1--2) used in the Vz dimension argument.
The kernel in `faithful` is relative to KO, not to the full Mathieu group. -/
structure CodeOctadCenterAction (O : Octad) : Prop where
  moved_finrank : Module.finrank (ZMod 2) (codeOctadMoved O) = 5
  displacement : ∀ a ∈ octadKernel O, ∀ v ∈ codeOctadMoved O,
    MathieuCode.codeRepresentation a v - v ∈
      fixedSpace MathieuCode.codeRepresentation (octadKernel O)
  faithful : subspaceKernel MathieuCode.codeRepresentation (codeOctadMoved O)
    (octadKernel O) = ⊥

/-- Central elements of a compatible Sylow subgroup belong to the source octad two-core. -/
theorem code_sylow_center_mem_octadKernel (O : Octad) (T : Sylow 2 M24)
    (hT : (T : Subgroup M24) ≤ octadStabilizer O) (z : M24)
    (hz : z ∈ (Subgroup.center T).map (T : Subgroup M24).subtype) :
    z ∈ octadKernel O := by
  change z ∈ (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype
  rw [MathieuCode.octad_core_map_eq_pointwise]
  exact MathieuCode.sylow_center_mem_octad_pointwiseKernel O T hT z hz

/-- The full element centralizer preserves the octad, using its actual fixed points. -/
theorem codeInvolution_centralizer_le_octadStabilizer (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Subgroup.centralizer ({z} : Set M24) ≤ octadStabilizer O := by
  apply MathieuCode.octad_kernel_centralizer_le_stabilizer O z _ hne
  simpa only [octadKernel, MathieuCode.octad_core_map_eq_pointwise] using hz

/-- KO is contained in the intrinsic two-core of C_M(z). -/
theorem octadKernel_le_codeInvolutionCore (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    octadKernel O ≤ codeInvolutionCore z := by
  unfold octadKernel codeInvolutionCore at *
  rw [MathieuCode.octad_core_map_eq_pointwise] at hz ⊢
  exact MathieuCode.octad_kernel_le_involution_core O z hz hne

/-- The literal fixed space of a nonidentity octad-kernel involution has dimension seven. -/
theorem codeInvolutionFixed_finrank (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Module.finrank (ZMod 2) (codeInvolutionFixed z) = 7 := by
  apply MathieuCode.octad_kernel_involution_fixed_finrank O z _ hne
  simpa only [octadKernel, MathieuCode.octad_core_map_eq_pointwise] using hz

/-- H.16.2(6)'s dimension clause, conditional only on the indicated earlier flag/action clauses. -/
theorem codeOctadInvolutionFixed_finrank (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) = 4 := by
  have hline : Module.finrank (ZMod 2)
      (fixedSpace MathieuCode.codeRepresentation (octadKernel O)) = 1 := by
    rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
    exact MathieuCode.octad_fixedSpace_finrank O
  have hmove : ∃ v ∈ codeOctadMoved O, MathieuCode.codeRepresentation z v ≠ v := by
    by_contra hn
    push Not at hn
    have hm : z ∈ subspaceKernel MathieuCode.codeRepresentation (codeOctadMoved O)
        (octadKernel O) := ⟨hz, hn⟩
    rw [h.faithful, Subgroup.mem_bot] at hm
    exact hne hm
  have hd := finrank_inf_fixedSpace_of_line_displacement MathieuCode.codeRepresentation
    (codeOctadMoved O) (fixedSpace MathieuCode.codeRepresentation (octadKernel O)) z
    hline (h.displacement z hz) hmove
  change Module.finrank (ZMod 2) (codeOctadInvolutionFixed O z) + 1 =
    Module.finrank (ZMod 2) (codeOctadMoved O) at hd
  rw [h.moved_finrank] at hd
  omega

/-- The centralizer preserves the actual involution fixed space. -/
theorem codeInvolutionFixed_stable (z : M24) :
    Subgroup.centralizer ({z} : Set M24) ≤
      subspaceStabilizer MathieuCode.codeRepresentation (codeInvolutionFixed z) := by
  apply le_subspaceStabilizer
  intro g hg v hv
  apply (mem_fixedSpace_zpowers_iff _ z _).mpr
  have hf := (mem_fixedSpace_zpowers_iff _ z v).mp hv
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply, hf]

/-- The centralizer preserves Vz, using relative normality of the octad kernel. -/
theorem codeOctadInvolutionFixed_stable (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Subgroup.centralizer ({z} : Set M24) ≤ subspaceStabilizer
      MathieuCode.codeRepresentation (codeOctadInvolutionFixed O z) := by
  have hn : Subgroup.centralizer ({z} : Set M24) ≤ Subgroup.normalizer (octadKernel O) := by
    rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
    exact (codeInvolution_centralizer_le_octadStabilizer O z hz hne).trans
      (MathieuCode.octad_stabilizer_le_normalizer_pointwiseKernel O)
  have hm := subspaceCommutator_invariant_normalizer MathieuCode.codeRepresentation
    (D := ⊤) (le_subspaceStabilizer _ _ (fun _ _ _ _ => Submodule.mem_top)) hn
  apply le_subspaceStabilizer
  intro g hg v hv
  exact ⟨(hm hg v).mpr hv.1, (codeInvolutionFixed_stable z hg v).mpr hv.2⟩

/-- A literal transvection on C_V(z) either centralizes Vz or acts trivially on its quotient.
The second alternative says exactly that every displacement belongs to Vz. -/
theorem codeInvolution_rank_one_alternative (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) (g : M24)
    (hg : g ∈ Subgroup.centralizer ({z} : Set M24))
    (ht : Module.finrank (ZMod 2) (LinearMap.range
      ((MathieuCode.codeRepresentation g - LinearMap.id).comp
        (codeInvolutionFixed z).subtype)) = 1) :
    g ∈ codeOctadInvolutionCentralizer O z ∨
      ∀ v ∈ codeInvolutionFixed z,
        MathieuCode.codeRepresentation g v - v ∈ codeOctadInvolutionFixed O z := by
  rcases rank_one_displacement_alternative MathieuCode.codeRepresentation
    (codeInvolutionFixed z) (codeOctadInvolutionFixed O z) g inf_le_right
    (fun v hv => (codeOctadInvolutionFixed_stable O z hz hne hg v).mpr hv) ht with h | h
  · exact Or.inl ⟨Subgroup.mem_top _, h⟩
  · exact Or.inr h

/-- The alternative stated on the actual representation of the fixed-space stabilizer. -/
theorem codeInvolution_transvection_alternative (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) (g : M24)
    (hg : g ∈ Subgroup.centralizer ({z} : Set M24))
    (ht : fixedCodim
      (stabilizerRepresentation MathieuCode.codeRepresentation (codeInvolutionFixed z))
      (Subgroup.zpowers ⟨g, codeInvolutionFixed_stable z hg⟩) = 1) :
    g ∈ codeOctadInvolutionCentralizer O z ∨
      ∀ v ∈ codeInvolutionFixed z,
        MathieuCode.codeRepresentation g v - v ∈ codeOctadInvolutionFixed O z := by
  apply codeInvolution_rank_one_alternative O z hz hne g hg
  rwa [fixedCodim_stabilizer_zpowers_eq_ambient_displacement] at ht

/-- The literal H.16.2(7) dimension formula follows from common-center displacement
and the cyclic action kernel. These two action premises remain explicit: this
is the assembly step, not an unconditional assertion of the source clause. -/
theorem codeInvolution_fixed_rank_of_common_center (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (horder : orderOf z = 2)
    (B : Subgroup M24) [IsElementaryAbelian 2 B]
    (hzB : z ∈ B) (hBC : B ≤ Subgroup.centralizer ({z} : Set M24))
    (hdisplacement : ∀ b ∈ B, ∀ v ∈ codeInvolutionFixed z,
      MathieuCode.codeRepresentation b v - v ∈
        fixedSpace MathieuCode.codeRepresentation (octadKernel O))
    (hkernel : subspaceKernel MathieuCode.codeRepresentation (codeInvolutionFixed z) B =
      Subgroup.zpowers z) :
    Module.finrank (ZMod 2) (fixedSpace MathieuCode.codeRepresentation B) = 8 - rank B := by
  have hne : z ≠ 1 := by intro he; subst z; simp at horder
  have hline : Module.finrank (ZMod 2)
      (fixedSpace MathieuCode.codeRepresentation (octadKernel O)) = 1 := by
    rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
    exact MathieuCode.octad_fixedSpace_finrank O
  have hLW : fixedSpace MathieuCode.codeRepresentation (octadKernel O) ≤
      codeInvolutionFixed z :=
    fixedSpace_antitone _ (Subgroup.zpowers_le.mpr hz)
  have hLB : fixedSpace MathieuCode.codeRepresentation (octadKernel O) ≤
      fixedSpace MathieuCode.codeRepresentation B := by
    rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
    exact (MathieuCode.octad_fixedSpace_le_stabilizer_fixedSpace O).trans
      (fixedSpace_antitone _ (hBC.trans (codeInvolution_centralizer_le_octadStabilizer O z hz hne)))
  have hBW : fixedSpace MathieuCode.codeRepresentation B ≤ codeInvolutionFixed z :=
    fixedSpace_antitone _ (Subgroup.zpowers_le.mpr hzB)
  have hd := finrank_fixedSpace_add_rank_of_common_center MathieuCode.codeRepresentation
    (codeInvolutionFixed z) (fixedSpace MathieuCode.codeRepresentation (octadKernel O)) B
    (hBC.trans (codeInvolutionFixed_stable z)) hLW hline hdisplacement hLB
  rw [inf_eq_right.mpr hBW, codeInvolutionFixed_finrank O z hz hne, hkernel] at hd
  have hr : rank (Subgroup.zpowers z) = 1 := by
    simp only [rank, Nat.card_zpowers, horder]
    decide
  rw [hr] at hd
  omega

end CFSG.Quasithin.ChapterH.Section13To16
