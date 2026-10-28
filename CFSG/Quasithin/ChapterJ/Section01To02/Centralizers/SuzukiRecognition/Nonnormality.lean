module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Residual
public import Theory.GroupTheory.SylowKernelCore
import Mathlib.Tactic.Group

/-!
# Fusion and the nonnormality step of J.2.9

The earlier equality sᴳ∩H=sᴴ, with H=C_G(z), reverses the roles of s
and z: zᴳ∩C_G(s) is one C_G(s)-class. Transporting a non-core member
of that class from a conjugate centralizer therefore puts z outside
O₂(C_G(s)). If V were normal in L_s, relative core monotonicity would
put V, and hence z, in this two-core.

The non-core witness is kept explicit. The source obtains it from the
J.2.7(7) subgroup Z₂×Sz(2); this module does not substitute the witness
for that model calculation.

Source: Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalSetup G} (c : Choices d)

/-- The simultaneous-conjugacy argument A.1.7(1) in this source situation. -/
theorem z_fusion_in_Gs
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h * c.s * h⁻¹ = t)
    {v : G} (hv : v ∈ c.Gs) (hconj : IsConj c.z v) :
    ∃ k ∈ c.Gs, k * c.z * k⁻¹ = v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let t := g⁻¹ * c.s * g
  have ht : t ∈ d.toTypeRuSetup.H := by
    rw [← hH]
    apply mem_centralizer_singleton_iff.mpr
    have hc := mem_centralizer_singleton_iff.mp hv
    rw [← hg] at hc
    have he := congrArg (fun x => g⁻¹ * x * g) hc
    dsimp [t]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he.symm
  have hst : IsConj c.s t := isConj_iff.mpr ⟨g⁻¹, by simp [t]⟩
  obtain ⟨h, hh, he⟩ := hsfusion t ht hst
  have hhz := mem_centralizer_singleton_iff.mp (hH.symm ▸ hh)
  refine ⟨g * h, ?_, ?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    have hc : (g * h) * c.s * (g * h)⁻¹ = c.s := by
      calc
        _ = g * (h * c.s * h⁻¹) * g⁻¹ := by group
        _ = g * t * g⁻¹ := by rw [he]
        _ = c.s := by dsimp [t]; group
    exact mul_inv_eq_iff_eq_mul.mp hc
  · calc
      _ = g * (h * c.z * h⁻¹) * g⁻¹ := by group
      _ = g * c.z * g⁻¹ := by rw [hhz, mul_inv_cancel_right]
      _ = v := hg

omit [Finite G] in
private theorem map_element_centralizer (f : MulAut G) (s : G) :
    (centralizer ({s} : Set G)).map f.toMonoidHom = centralizer ({f s} : Set G) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({s} : Set G) f.toMonoidHom
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- The non-core witness at a conjugate of s excludes z from O₂(C_G(s)). -/
theorem z_not_mem_twoCore_of_local_witness
    (hH : centralizer ({c.z} : Set G) = d.toTypeRuSetup.H)
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h * c.s * h⁻¹ = t)
    {t v : G} (hst : IsConj c.s t) (hv : v ∈ centralizer ({t} : Set G))
    (hzv : IsConj c.z v) (hvn : v ∉ (centralizer ({t} : Set G)).pCoreIn 2) :
    c.z ∉ c.Gs.pCoreIn 2 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hst
  let f := MulAut.conj g
  have hft : f c.s = t := hg
  have hC : c.Gs.map f.toMonoidHom = centralizer ({t} : Set G) := by
    rw [show c.Gs = centralizer ({c.s} : Set G) from rfl, map_element_centralizer, hft]
  have hw : f.symm v ∈ c.Gs := by
    have hm : v ∈ c.Gs.map f.toMonoidHom := hC.symm ▸ hv
    obtain ⟨w, hw, rfl⟩ := hm
    change f.symm (f w) ∈ c.Gs
    rwa [f.symm_apply_apply]
  have hzw : IsConj c.z (f.symm v) :=
    hzv.trans (isConj_iff.mpr ⟨g⁻¹, by simp [f, MulAut.conj_symm_apply]⟩)
  obtain ⟨k, hk, he⟩ := c.z_fusion_in_Gs hH hsfusion hw hzw
  have hnorm : c.Gs ≤ normalizer (c.Gs.pCoreIn 2 : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_characteristic_image c.Gs (pCore 2 c.Gs))
  intro hz
  have hwcore : f.symm v ∈ c.Gs.pCoreIn 2 := he ▸ (hnorm hk c.z).mp hz
  apply hvn
  have hm := mem_map_of_mem f.toMonoidHom hwcore
  rw [map_pCoreIn_of_injective 2 c.Gs f.toMonoidHom f.injective, hC] at hm
  simpa only [MulEquiv.coe_toMonoidHom, f.apply_symm_apply] using hm

/-- Nonnormality of V in the residual follows from the two-core exclusion. -/
theorem V_normalizer_ne_top_of_z_not_mem_twoCore
    (hVL : d.V ≤ c.Ls) (hzV : c.z ∈ d.V) (hzn : c.z ∉ c.Gs.pCoreIn 2) :
    normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤ := by
  intro hn
  have hVLn : c.Ls ≤ normalizer (d.V : Set G) := by
    intro x hx
    have h : (⟨x, hx⟩ : c.Ls) ∈ normalizer (d.V.subgroupOf c.Ls : Set c.Ls) := by
      rw [hn]; trivial
    rw [← subgroupOf_normalizer_eq hVL] at h
    exact h
  have hp : IsPGroup 2 d.V := by
    intro x
    exact ⟨1, by simpa using d.ru1.natural.square_eq_one_of_trivial_kernel rfl x⟩
  have hcore : d.V ≤ c.Ls.pCoreIn 2 := le_pCoreIn_of_normalizes hp hVL hVLn
  exact hzn ((hcore.trans (pCoreIn_mono_of_normalizes c.Ls_le_Gs c.Gs_normalizes_Ls)) hzV)

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
