module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.Native
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.AlphaGroups
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.NativeFixers
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.AmbientContainment
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorReduction

/-!
# Tensor involutions and Sylow pointwise fixers in K.3.4.2

The native tensor calculations give fixed dimensions 10s for b₁ and 8s for
both a₂ and c₂, together with intrinsic freeness for the last two types.
These results use the genuine scalar-extension identification and do not
require an ambient diagram hypothesis.

Under the source hypotheses and the permitted diagram-preservation premise,
ambient displacement fixers lie in the component. The component calculation
identifies the full fixer with the transported alpha line having sigma-fixed
parameters and proves its order is 2^s. Intersecting with the literal Sylow
subgroup gives the required rank bound. Native freeness gives the corresponding
fixed-space fixer for a₂ and c₂. For a normalized involution commuting with
sigma, the coefficient-fixed line is exactly the sigma-fixed subgroup of the
source alpha group. Its two coordinate axes are root groups; c₂ retains the
alpha-group convention.

The final theorem supplies the exact local bounds to the existing quadratic
obstruction. Diagram preservation and actor placement remain with the source
assembly owner; this module does not assert the whole K.3.4.2 classification.

Sources: Aschbacher–Smith, printed pp.456–457 (PDF pp.467–468);
Aschbacher–Seitz, *Involutions in Chevalley groups over fields of even order*,
§11, printed p.30, DOI 10.1017/S0027763000017438.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
open Representation.OneCohomology.SymplecticFour

namespace CFSG.Quasithin.ChapterK.Symplectic
open TensorGeometry
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- The full component fixer in the original ambient group, with the literal
conjugation and inclusion maps from a specified central normal form. -/
theorem TensorIdentification.component_displacementKernel_eq_centralSigmaAlpha
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (c : Sp F) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0)
    (hc : c * h.groupEquiv ⟨j, hjL⟩ * c⁻¹ = rootElement 0 a * rootElement 4 b) :
    subspaceKernel ρ (LinearMap.range (displacement ρ j)) L =
      (centralSigmaAlpha h.sigma.toRingEquiv a b).map
        (L.subtype.comp (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom) := by
  have he := h.displacement_fixer_eq_centralSigmaAlpha (ρ.comp L.subtype)
    ⟨j, hjL⟩ c a b hab hc
  have hm : subspaceKernel ρ (LinearMap.range (displacement ρ j)) L =
      (subspaceKernel (ρ.comp L.subtype)
        (LinearMap.range (displacement (ρ.comp L.subtype) ⟨j, hjL⟩)) ⊤).map L.subtype := by
    ext g
    constructor
    · rintro ⟨hg, hf⟩
      exact ⟨⟨g, hg⟩, ⟨Subgroup.mem_top _, hf⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.property, hg.2⟩
  rw [hm, he, Subgroup.map_map]

variable {K : GroupClass} (hS : SourceHypothesis K ρ L)
  {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
  (hdiagram :
    letI : L.Normal := by
      let : Finite G := hS.finite_group
      rw [← hS.fitting]
      infer_instance
    ∀ g : G, PreservesDiagram (extensionAction L h.groupEquiv.symm g))

include hS h hdiagram

/-- Ambient containment identifies every pointwise displacement fixer with
the intersection with the full component fixer. -/
theorem TensorIdentification.displacementKernel_eq_inf_component
    (A : Subgroup G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2) :
    subspaceKernel ρ (LinearMap.range (displacement ρ j)) A =
      A ⊓ subspaceKernel ρ (LinearMap.range (displacement ρ j)) L := by
  ext g
  constructor
  · intro hg
    refine ⟨hg.1, ?_, hg.2⟩
    exact h.displacement_fixer_mem_component hS hdiagram j hjL hj g
      (fun v => hg.2 _ ⟨v, rfl⟩)
  · rintro ⟨hg, _, hf⟩
    exact ⟨hg, hf⟩

/-- The literal Sylow displacement fixer is the intersection with the
transported coefficient-fixed alpha line. No root-type assumption is imposed. -/
theorem TensorIdentification.sylow_displacementKernel_eq_centralSigmaAlpha
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2)
    (c : Sp F) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0)
    (hc : c * h.groupEquiv ⟨j, hjL⟩ * c⁻¹ = rootElement 0 a * rootElement 4 b) :
    subspaceKernel ρ (LinearMap.range (displacement ρ j)) T =
      (T : Subgroup G) ⊓ (centralSigmaAlpha h.sigma.toRingEquiv a b).map
        (L.subtype.comp (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom) := by
  rw [h.displacementKernel_eq_inf_component hS hdiagram T j hjL hj,
    h.component_displacementKernel_eq_centralSigmaAlpha j hjL c a b hab hc]

/-- For a central form commuting with the coefficient involution, the
alpha-line factor is exactly its sigma-fixed subgroup. On the two axes,
`centralAlpha_left_eq_root` and `centralAlpha_right_eq_root` identify the
actual root groups; in type c₂ it remains the alpha group of AS76a §11. -/
theorem TensorIdentification.sylow_displacementKernel_mem_iff_sigma_fixed
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2)
    (c : Sp F) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0)
    (hc : c * h.groupEquiv ⟨j, hjL⟩ * c⁻¹ = rootElement 0 a * rootElement 4 b)
    (ha : h.sigma a = a) (hb : h.sigma b = b) (g : L) :
    (g : G) ∈ subspaceKernel ρ (LinearMap.range (displacement ρ j)) T ↔
      (g : G) ∈ T ∧
        c * h.groupEquiv g * c⁻¹ ∈ centralAlpha a b ∧
          fieldAutomorphism h.sigma.toRingEquiv (c * h.groupEquiv g * c⁻¹) =
            c * h.groupEquiv g * c⁻¹ := by
  have hmap (U : Subgroup L) : (g : G) ∈ U.map L.subtype ↔ g ∈ U := by
    constructor
    · rintro ⟨u, hu, he⟩
      exact (Subtype.ext he : u = g) ▸ hu
    · intro hg
      exact ⟨g, hg, rfl⟩
  rw [h.sylow_displacementKernel_eq_centralSigmaAlpha hS hdiagram T j hjL hj c a b hab hc,
    Subgroup.mem_inf, ← Subgroup.map_map, hmap, Subgroup.mem_map_equiv]
  exact and_congr_right fun _ => mem_centralSigmaAlpha_iff_fixed
    h.sigma.toRingEquiv hab ha hb _

/-- Every native involution has this concrete Sylow fixer after the proved
group conjugacy normal form, without an additional normal-form premise. -/
theorem TensorIdentification.sylow_involution_displacement_fixer
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2) :
    ∃ (c : Sp F) (a b : F), (a ≠ 0 ∨ b ≠ 0) ∧
      c * h.groupEquiv ⟨j, hjL⟩ * c⁻¹ = rootElement 0 a * rootElement 4 b ∧
      subspaceKernel ρ (LinearMap.range (displacement ρ j)) T =
        (T : Subgroup G) ⊓ (centralSigmaAlpha h.sigma.toRingEquiv a b).map
          (L.subtype.comp (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom) := by
  have ho : orderOf (⟨j, hjL⟩ : L) = 2 :=
    (Subgroup.orderOf_coe (⟨j, hjL⟩ : L)).symm.trans hj
  obtain ⟨c, a, b, hab, hc, _⟩ :=
    h.involution_displacement_fixer (ρ.comp L.subtype) ⟨j, hjL⟩ ho
  exact ⟨c, a, b, hab, hc,
    h.sylow_displacementKernel_eq_centralSigmaAlpha hS hdiagram T j hjL hj c a b hab hc⟩

/-- For a₂ and c₂, native freeness gives the same literal description of
the pointwise fixed-space fixer. -/
theorem TensorIdentification.sylow_nonB1_fixedSpace_fixer
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv ⟨j, hjL⟩)) :
    ∃ (c : Sp F) (a b : F), (a ≠ 0 ∨ b ≠ 0) ∧
      c * h.groupEquiv ⟨j, hjL⟩ * c⁻¹ = rootElement 0 a * rootElement 4 b ∧
      subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T =
        (T : Subgroup G) ⊓ (centralSigmaAlpha h.sigma.toRingEquiv a b).map
          (L.subtype.comp (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom) := by
  let : Finite G := hS.finite_group
  rw [h.component_nonB1_fixedSpace_eq_displacement ρ L j hjL hj hB]
  exact h.sylow_involution_displacement_fixer hS hdiagram T j hjL hj

/-- The component fixer has order 2^s, so its intersection with any
ambient Sylow subgroup has binary rank at most s. -/
theorem TensorIdentification.sylow_displacementKernel_rank_le
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2) :
    rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) ≤ s := by
  let : Finite G := hS.finite_group
  have hle : subspaceKernel ρ (LinearMap.range (displacement ρ j)) T ≤
      subspaceKernel ρ (LinearMap.range (displacement ρ j)) L := by
    rw [h.displacementKernel_eq_inf_component hS hdiagram T j hjL hj]
    exact inf_le_right
  have hc := Subgroup.card_le_of_le hle
  rw [h.component_involution_displacement_fixer_card ρ L j hjL hj] at hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using Nat.log_mono_right (b := 2) hc

/-- The fixed-space pointwise-fixer bound for every non-b₁ involution,
on the original binary representation. -/
theorem TensorIdentification.sylow_nonB1_fixedKernel_rank_le
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv ⟨j, hjL⟩)) :
    rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) ≤ s := by
  let : Finite G := hS.finite_group
  rw [h.component_nonB1_fixedSpace_eq_displacement ρ L j hjL hj hB]
  exact h.sylow_displacementKernel_rank_le hS hdiagram T j hjL hj

/-- The fixed-space fixer estimate for the actual a₂ predicate after the
given group identification. -/
theorem TensorIdentification.sylow_isA2_fixedKernel_rank_le
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : IsA2 (h.groupEquiv ⟨j, hjL⟩)) :
    rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) ≤ s := by
  let : Finite G := hS.finite_group
  rw [h.component_isA2_fixedSpace_eq_displacement ρ L j hjL hj]
  apply h.sylow_displacementKernel_rank_le hS hdiagram T j hjL
  exact (Subgroup.orderOf_coe (⟨j, hjL⟩ : L)).trans
    ((h.groupEquiv.orderOf_eq _).symm.trans hj.1)

/-- The fixed-space fixer estimate for the actual c₂ predicate; its
component fixer is an alpha group, with no root-group identification assumed. -/
theorem TensorIdentification.sylow_isC2_fixedKernel_rank_le
    (T : Sylow 2 G) (j : G) (hjL : j ∈ L) (hj : IsC2 (h.groupEquiv ⟨j, hjL⟩)) :
    rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) ≤ s := by
  let : Finite G := hS.finite_group
  rw [h.component_isC2_fixedSpace_eq_displacement ρ L j hjL hj]
  apply h.sylow_displacementKernel_rank_le hS hdiagram T j hjL
  exact (Subgroup.orderOf_coe (⟨j, hjL⟩ : L)).trans
    ((h.groupEquiv.orderOf_eq _).symm.trans hj.1)

/-- The exact local premise of `TensorIdentification.quadraticRatio_gt_two`.
The fixed dimension comes from the unconditional native calculation; the
fixer bound combines the concrete component calculation and ambient containment. -/
theorem TensorIdentification.involution_local_bounds :
    ∀ (T : Sylow 2 G) (j : G), j ∈ T → j ∈ L → orderOf j = 2 →
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers j)) ≤ 10 * s ∧
        rank (subspaceKernel ρ (LinearMap.range (displacement ρ j)) T) ≤ s := by
  let : Finite G := hS.finite_group
  intro T j _ hjL hj
  exact ⟨h.component_involution_fixed_finrank_le ρ L j hjL hj,
    h.sylow_displacementKernel_rank_le hS hdiagram T j hjL hj⟩

/-- Apply the local calculations to the original quadratic-ratio consumer.
Only the independently owned diagram preservation and actor placement remain
explicit; no local dimension, fixer, or cardinality certificates remain. -/
theorem TensorIdentification.quadraticRatio_gt_two_of_diagram_and_placement
    (hs : 0 < s)
    (hplace : ∀ A, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L) :
    2 < quadraticRatio ρ := by
  let : Finite G := hS.finite_group
  exact h.quadraticRatio_gt_two ρ hs hplace (h.involution_local_bounds hS hdiagram)

end CFSG.Quasithin.ChapterK.Symplectic
