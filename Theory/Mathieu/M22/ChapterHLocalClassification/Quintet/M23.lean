module
public import Theory.Mathieu.M22.ChapterHLocalClassification
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores
/-!
# The actual inner M22 quintet inside the M23 quintet

The source sextet conjugator fixes the distinguished native point, hence
lifts to M23. Conjugating the original M22 inclusion by that lift sends
the restricted sextet core into the M23 quintet core. Both have order
sixteen, so the core image is exactly equal. All maps are literal native
inclusions and conjugations.

Source: Aschbacher–Smith H.14.2(2) and H.14.3(2), printed p.397; used in
the Mathieu rows of 2.4.25, printed p.543.
-/

public section
open Subgroup Sporadic.Mathieu MathieuCode
namespace Sporadic.Mathieu.M22ChapterH.Quintet

private theorem geometryConjugator_fixed_zero :
    m22GeometryConjugator.val 0 = 0 := by decide +kernel

noncomputable def sourceConjugator : M23 :=
  ((pointEmbedding_range ▸ (show m22GeometryConjugator ∈ MulAction.stabilizer M24 (0 : Fin 24)
    from geometryConjugator_fixed_zero)) : m22GeometryConjugator ∈ pointEmbedding.range).choose

theorem sourceConjugator_embedding : pointEmbedding sourceConjugator = m22GeometryConjugator :=
  ((pointEmbedding_range ▸ (show m22GeometryConjugator ∈ MulAction.stabilizer M24 (0 : Fin 24)
    from geometryConjugator_fixed_zero)) : m22GeometryConjugator ∈ pointEmbedding.range).choose_spec

noncomputable def quintetInM23 : M22 →* M23 :=
  (MulAut.conj sourceConjugator⁻¹).toMonoidHom.comp m22InM23

theorem quintetInM23_injective : Function.Injective quintetInM23 :=
  (MulAut.conj sourceConjugator⁻¹).injective.comp
    (fun _ _ h => m22Embedding_injective (congrArg pointEmbedding h))

theorem quintetInM23_embedding (g : M22) : pointEmbedding (quintetInM23 g) =
    (MulAut.conj m22GeometryConjugator⁻¹) (m22Embedding g) := by
  change pointEmbedding (sourceConjugator⁻¹ * m22InM23 g * (sourceConjugator⁻¹)⁻¹) =
    m22GeometryConjugator⁻¹ * pointEmbedding (m22InM23 g) * (m22GeometryConjugator⁻¹)⁻¹
  simp only [map_mul,map_inv,sourceConjugator_embedding]

/-- The literal inner quintet core maps onto the actual M23 quintet core. -/
theorem inner_core_image :
    (m22InnerQuintetKernel m22SourceSextet).map quintetInM23 =
      (pCore 2 M23Geometry.CommonFour.quintetStabilizer).map
        M23Geometry.CommonFour.quintetStabilizer.subtype := by
  have he : (MulAut.conj m22GeometryConjugator⁻¹).toMonoidHom.comp
      (MulAut.conj m22GeometryConjugator).toMonoidHom = MonoidHom.id M24 := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hmap : Sextet.sourceCore.map (MulAut.conj m22GeometryConjugator⁻¹).toMonoidHom =
      M24LocalGeometry.SextetCore.core := by
    rw [Sextet.sourceCore_eq_conjugate,map_map,he,map_id]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a,ha,rfl⟩
    rw [M23Geometry.CommonFour.quintet_core_eq,←M23Geometry.CommonFour.sextet_core_comap]
    change pointEmbedding (quintetInM23 a) ∈ M24LocalGeometry.SextetCore.core
    rw [quintetInM23_embedding,←hmap]
    apply mem_map_of_mem
    rw [←innerTranslations_eq_core] at ha
    exact ha
  · rw [card_map_of_injective quintetInM23_injective,inner_core_card,
      M23Geometry.CommonFour.quintet_core_eq,M23Geometry.CommonFour.standardCandidate_card]
end Sporadic.Mathieu.M22ChapterH.Quintet
