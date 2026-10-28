module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.NormalizerAction.OmegaCenterCentralizer

/-!
# Centralizers of seeds surviving the ambient two-core

In an SQTK two-core quotient, a nonnormal C-component has a centerless
ordinary-component image. A seed surviving the two-core is therefore
noncentral in that image. Component commutation forces its centralizer to
normalize the image, and uniqueness of C-component lifting returns the
original normalizer. Normal components need no quotient argument.

This includes constrained components and uses the earlier nonnormal-source
theorem rather than asserting that every quasisimple quotient is centerless.
Source: Aschbacher--Smith, A.3.8(3), 1.2.1(3), and 15.1.22(**),
printed pp.45--46,504,1099.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

theorem cComponent_centralizer_le_normalizer_of_not_le_twoCore
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {B Y : Subgroup G} (hB : B.IsCComponent) (hYB : Y ≤ B)
    (hout : ¬ Y ≤ pCore 2 G) :
    centralizer (Y : Set G) ≤ normalizer (B : Set G) := by
  classical
  by_cases hn : B.Normal
  · let := hn
    exact le_normalizer_of_normal
  let q := QuotientGroup.mk' (pCore 2 G)
  let K := B.map q
  let := pCore_isNilpotent (p := 2) (G := G)
  have hk := nonnormal_twoCore_image_isComponent hQ hB hn
  have hnon : ¬ K.Normal := fun hb => hn
    (cComponent_normal_of_quotient_normal hB (pCore 2 G) hb)
  let : IsQuasisimple K := hk.2
  have hf : fittingSubgroup K ≤ center K :=
    (le_solvableRadical _ inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hQ K
    (hB.map_quotient (pCore 2 G)) hf).2
  have hz := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_eq_bot_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) K hk hnon hm
  have hnc : ¬ Y.map q ≤ centralizer (K : Set (G ⧸ pCore 2 G)) := by
    intro hc
    apply hout
    intro y hy
    apply (QuotientGroup.eq_one_iff (N := pCore 2 G) y).mp
    let k : K := ⟨q y, mem_map_of_mem q (hYB hy)⟩
    have hkZ : k ∈ center K := mem_center_iff.mpr (fun b =>
      Subtype.ext (hc (mem_map_of_mem q hy) b b.property))
    have he : k = 1 := by simpa only [hz, mem_bot] using hkZ
    exact congrArg (fun b : K => (b : G ⧸ pCore 2 G)) he
  rw [← normalizer_cComponent_quotient hB (pCore 2 G)]
  intro x hx
  apply hk.centralizer_le_normalizer_of_noncentral (Y.map q) (map_mono hYB) hnc
  rintro _ ⟨y,hy,rfl⟩
  exact congrArg q (hx y hy)
end CFSG.Quasithin.Chapter1.Section02
