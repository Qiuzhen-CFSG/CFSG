module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanImage
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Normality of the residual in the local vertex

The earlier equality C_G(V₂)=C_H(V₂) identifies Y with the two-residual
of the full ambient centralizer. Characteristicity of the residual and
normality of the centralizer in N_G(V₂) give the required relative normality.
The actual conjugation maps then carry this to normality of the Y-image
inside the vertex image and containment of their two-cores.

This discharges the image-normality input of the span calculation from the
earlier source centralizer identity. It imposes no ambient normality on Y.
The two-core of the Y-image must still be proved nontrivial.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
14.7.56(2), printed p.1066; Y=O²(C_H(V₂)) is defined in 14.7.55(6).
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ResidualAction

open Subgroup
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
variable {G : Type*} [Group G]

/-- Y is normalized by the actual local vertex because it is characteristic
in its normal centralizer. -/
theorem source_residual_normalized_by_vertex (H V₂ : Subgroup G)
    (hC : centralizer (V₂ : Set G) ≤ H) :
    normalizer (V₂ : Set G) ≤ normalizer (localResidual H V₂ : Set G) := by
  have hn : normalizer (V₂ : Set G) ≤ normalizer (centralizer (V₂ : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance
  rw [localResidual, inf_eq_right.mpr hC]
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- Normality transfers through the two compatible literal conjugation actions. -/
theorem ambient_action_normal_image (N Y W : Subgroup G)
    (hYN : Y ≤ N) (hNY : N ≤ normalizer (Y : Set G))
    (hNW : N ≤ normalizer (W : Set G)) :
    (ambientAction N W hNW).range ≤
      normalizer ((ambientAction Y W (hYN.trans hNW)).range : Set (MulAut W)) := by
  let ρ := ambientAction N W hNW
  have he : (Y.subgroupOf N).map ρ = (ambientAction Y W (hYN.trans hNW)).range := by
    ext a
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y.val,hy⟩,rfl⟩
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y.val,hYN y.property⟩,y.property,rfl⟩
  have hn := (normal_subgroupOf_iff_le_normalizer hYN).mpr hNY
  have hm := (Y.subgroupOf N).le_normalizer_map ρ
  rw [normalizer_eq_top_iff.mpr hn, ← MonoidHom.range_eq_map,he] at hm
  exact hm

/-- The source centralizer identity supplies containment of the Y-image
two-core in the local-vertex image two-core. -/
theorem source_residual_action_core_le (H V V₂ Y : Subgroup G)
    (hY : Y = localResidual H V₂) (hC : centralizer (V₂ : Set G) ≤ H)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (hYV : Y ≤ normalizer (V₂ : Set G)) :
    (ambientAction Y (generatedLineFamily V Y) (hYV.trans hspan)).range.pCoreIn 2 ≤
      (ambientAction (normalizer (V₂ : Set G)) (generatedLineFamily V Y) hspan).range.pCoreIn 2 := by
  have hn : normalizer (V₂ : Set G) ≤ normalizer (Y : Set G) := by
    rw [hY]
    exact source_residual_normalized_by_vertex H V₂ hC
  exact local_residual_two_core_le_vertex_two_core V V₂ Y hYV hspan
    (ambient_action_normal_image _ _ _ hYV hn hspan)

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ResidualAction
