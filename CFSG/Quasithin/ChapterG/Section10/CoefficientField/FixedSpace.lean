module
public import CFSG.Quasithin.ChapterG.Section10.CoefficientField

/-!
# Commuting automorphisms and the marked fixed space

If a linear automorphism centralizing the original actor moves the marked
point, the full transvection spaces W and its image are disjoint. The actor
fixes the intersection of the two marked hyperplanes, which has codimension
at most two. This also covers marked spaces of dimension one or two.

ComponentCatalogueLargeActorDegreesSymplectic applies this to a nonbinary
coefficient scalar and the literal natural symplectic actor.
Source: Aschbacher–Smith G.10.1 and the coefficient-field argument of G.11.7,
printed pp.357,367 of refs/quasithin.pdf.
-/
@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- A commuting linear automorphism moving the marked point forces fixed
codimension at most two. No lower bound on the marked-space dimension is needed. -/
theorem fixedCodim_le_two_of_centralizing_moves_point
    (J : V ≃ₗ[ZMod 2] V)
    (hJ : ∀ (x : X) w, ρ x (J w) = J (ρ x w))
    (hne : J v ≠ v) : fixedCodim ρ X ≤ 2 := by
  classical
  have haxis {w : V} (hv : w ∈ Submodule.span (ZMod 2) {v})
      (hj : w ∈ Submodule.span (ZMod 2) {J v}) : w = 0 := by
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hj
    fin_cases a <;> fin_cases b
    · change (0 : ZMod 2) • v = w at ha
      simpa only [zero_smul] using ha.symm
    · change (0 : ZMod 2) • v = w at ha
      simpa only [zero_smul] using ha.symm
    · change (0 : ZMod 2) • J v = w at hb
      simpa only [zero_smul] using hb.symm
    · change (1 : ZMod 2) • v = w at ha
      change (1 : ZMod 2) • J v = w at hb
      simp only [one_smul] at ha hb
      exact (hne (hb.trans ha.symm)).elim
  let U := W.map J.toLinearMap
  have hdiffW (x : X) (w : W) : ρ x w - w ∈ Submodule.span (ZMod 2) {v} := by
    obtain ⟨f,_,hf⟩ := h.transvections x
    rw [hf w,add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hdiffU (x : X) (u : V) (hu : u ∈ U) :
      ρ x u - u ∈ Submodule.span (ZMod 2) {J v} := by
    obtain ⟨w,hw,rfl⟩ := hu
    change ρ x (J w) - J w ∈ _
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hdiffW x ⟨w,hw⟩)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c,?_⟩
    calc
      c • J v = J (c • v) := (J.map_smul c v).symm
      _ = J (ρ x w - w) := congrArg J hc
      _ = ρ x (J w) - J w := by simp only [map_sub,hJ]
  have hinter : Disjoint W U := by
    apply Submodule.disjoint_def.mpr
    intro w hw hu
    have hf (x : X) : ρ x w = w := sub_eq_zero.mp
      (haxis (hdiffW x ⟨w,hw⟩) (hdiffU x w hu))
    have hwv := h.fixed_on_marked_space w hw hf
    obtain ⟨z,hz,hzw⟩ := hu
    have hzf (x : X) : ρ x z = z := by
      apply J.injective
      rw [← hJ]
      change ρ x (J z) = J z
      rw [show J z = w from hzw,hf]
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (h.fixed_on_marked_space z hz hzf)
    have hwj : w ∈ Submodule.span (ZMod 2) {J v} :=
      Submodule.mem_span_singleton.mpr ⟨c,by rw [← J.map_smul,hc]; exact hzw⟩
    exact haxis hwv hwj
  let f : V →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    (B v).prod ((B v).comp J.symm.toLinearMap)
  have hk : f.ker ≤ fixedSpace ρ X := by
    intro u hu x
    have hu1 : B v u = 0 := congrArg Prod.fst hu
    have hu2 : B v (J.symm u) = 0 := congrArg Prod.snd hu
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hinter
    · exact h.displacement x u hu1
    · refine ⟨ρ x (J.symm u) - J.symm u,h.displacement x (J.symm u) hu2,?_⟩
      change J (ρ x (J.symm u) - J.symm u) = ρ x u - u
      rw [map_sub,←hJ,J.apply_symm_apply]
  have hmono := Submodule.finrank_mono hk
  have hker := f.finrank_range_add_finrank_ker
  have hfixed := fixedCodim_add_finrank ρ X
  have hr : finrank (ZMod 2) f.range ≤ 2 := by
    simpa using Submodule.finrank_le f.range
  omega
end CFSG.Quasithin.ChapterG.Section10.Hypothesis
