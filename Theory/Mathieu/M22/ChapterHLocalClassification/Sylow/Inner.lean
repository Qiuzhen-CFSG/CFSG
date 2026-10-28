module
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Candidates
public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow

/-!
# The two elementary subgroups of order sixteen in the inner Sylow

The native embedding into M23 preserves the order-128 Sylow subgroup.
One Sylow conjugation in M23 puts every inner elementary subgroup into the
already certified M23 catalogue. Our two distinct source candidates exhaust
its two possible images, and injectivity pulls equality back to native M22.
No arbitrary elementary subgroup is assumed normal.

Source: Aschbacher--Smith H.14.2(1) and H.14.3(1), printed p.397.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow

/-- Reusing the exhaustive native M23 catalogue through the actual point embedding
classifies all inner E16 subgroups, without a normality assumption. -/
theorem inner_card16 (A : Subgroup M22) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) (hAS : A ≤ inner.toSubgroup) :
    A = m22InnerHexadKernel m22SourceOctad ∨ A = Sextet.innerTranslations := by
  have hf : Function.Injective m22InM23 :=
    fun _ _ h => m22Embedding_injective (congrArg pointEmbedding h)
  let P : Sylow 2 M23 := Sylow.ofCard (inner.toSubgroup.map m22InM23) (by
    rw [Subgroup.card_map_of_injective hf]
    change Nat.card innerGroup = _
    rw [innerGroup_card, m23_order]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 P M23Geometry.FusionCertificate.sylow
  let f : M22 →* M23 := (MulAut.conj g).toMonoidHom.comp m22InM23
  have hfi : Function.Injective f := (MulAut.conj g).injective.comp hf
  have hP : inner.toSubgroup.map f = M23Geometry.FusionCertificate.subgroup := by
    rw [show inner.toSubgroup.map f =
      (inner.toSubgroup.map m22InM23).map (MulAut.conj g).toMonoidHom from
        (Subgroup.map_map _ _ _).symm]
    exact congrArg Sylow.toSubgroup hg
  have classify (B : Subgroup M22) (hB : IsElementaryAbelian 2 B)
      (hBc : Nat.card B = 16) (hBS : B ≤ inner.toSubgroup) :
      B.map f = M23Geometry.ElementarySylow.candidate 0 ∨
      B.map f = M23Geometry.ElementarySylow.candidate 1 := by
    let _ := hB
    obtain ⟨b, hb⟩ := M23Geometry.ElementarySylow.card16_eq_candidate
      (B.map f) (IsElementaryAbelian.map f)
      ((Subgroup.card_map_of_injective hfi).trans hBc)
      (hP ▸ Subgroup.map_mono hBS)
    fin_cases b
    · exact Or.inl hb
    · exact Or.inr hb
  have ha := classify A hA hc hAS
  have hh := classify (m22InnerHexadKernel m22SourceOctad) Hexad.inner_kernel_elementary
    Hexad.inner_kernel_card innerHexad_le
  have ht := classify Sextet.innerTranslations innerTranslations_elementary
    innerTranslations_card innerTranslations_le
  have hn : (m22InnerHexadKernel m22SourceOctad).map f ≠ Sextet.innerTranslations.map f :=
    fun h => inner_candidates_distinct (Subgroup.map_injective hfi h)
  have he : A.map f = (m22InnerHexadKernel m22SourceOctad).map f ∨
      A.map f = Sextet.innerTranslations.map f := by
    rcases ha with ha | ha <;> rcases hh with hh | hh <;> rcases ht with ht | ht <;>
      first | exact (hn (hh.trans ht.symm)).elim | exact Or.inl (ha.trans hh.symm) |
        exact Or.inr (ha.trans ht.symm)
  exact he.imp (fun h => Subgroup.map_injective hfi h) (fun h => Subgroup.map_injective hfi h)

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow
