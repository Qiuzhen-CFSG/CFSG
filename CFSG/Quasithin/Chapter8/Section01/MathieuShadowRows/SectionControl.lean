module
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.PointNative
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Section control through the full M22 cocode point image

The original local action maps the point residual onto the linear subgroup
of PSL₃(4) extended by field Frobenius. Its entire two-core acts trivially.
Thus an element centralizing the residual modulo its two-core centralizes
the linear subgroup in the full model, and has trivial action. This supplies
the section-centralizer clause of C.2.8 in source 8.1.1 (p.712).
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Matrix.PSL3Four MathieuCode.NormalizedShadowRows
variable {G : Type*} [Group G]

/-- The literal section centralizer has trivial full point-model image. -/
theorem m22_point_section_le_kernel {A B : Subgroup G}
    (hBA : B ≤ A) (hAB : A ≤ normalizer (B : Set G))
    (f : A →* FieldExtension)
    (himage : (B.subgroupOf A).map f = linearInclusion.range) :
    ChapterA.Section04.twoSectionCentralizer B A ≤ f.ker.map A.subtype := by
  have hlinear : linearInclusion.range ≤ f.range := himage ▸ map_le_range f _
  have hkill := fieldExtension_twoCore_image f hlinear
  have hcore : B.pCoreIn 2 ≤ A.pCoreIn 2 := pCoreIn_mono_of_normalizes hBA hAB
  intro g hg
  have hgA : g ∈ A := hg.1
  refine ⟨⟨g,hgA⟩,?_,rfl⟩
  change f ⟨g,hgA⟩ = 1
  apply mem_bot.mp
  rw [←fieldExtension_centralizer_linear,←himage]
  apply mem_centralizer_iff.mpr
  rintro y ⟨b,hb,rfl⟩
  obtain ⟨c,hc,he⟩ := hcore (hg.2.2 b hb)
  have hcc : f c = 1 := hkill hc
  have hh : ⁅(⟨g,hgA⟩ : A),b⁆ = c := Subtype.ext he.symm
  have hh' := congrArg f hh
  rw [map_commutatorElement,hcc,commutatorElement_eq_one_iff_mul_comm] at hh'
  exact hh'.symm

/-- The original point centralizer keeps O₂(J), using its full native point
action image rather than assuming that image equals its linear residual. -/
theorem m22_point_core_eq (W J : Subgroup G)
    (hJN : J ≤ normalizer (W : Set G))
    (hQ : J.pCoreIn 2 ≤ centralizer (W : Set G)) (x : W)
    (f : (J ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* FieldExtension)
    (hlinear : linearInclusion.range ≤ f.range)
    (hker : f.ker = (centralizer (W : Set G)).subgroupOf
      (J ⊓ centralizer ({(x : G)} : Set G))) :
    (J ⊓ centralizer ({(x : G)} : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  let K := J ⊓ centralizer ({(x : G)} : Set G)
  let C := J ⊓ centralizer (W : Set G)
  have hc : centralizer (W : Set G) ≤ centralizer ({(x : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr x.property)
  have hkill := fieldExtension_twoCore_image f hlinear
  have hk : K.pCoreIn 2 ≤ centralizer (W : Set G) := by
    rintro y ⟨k,hk,rfl⟩
    have he : k ∈ f.ker := hkill hk
    rw [hker] at he
    exact he
  have hCK : C ≤ K := inf_le_inf_left J hc
  have hJC : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer (hJN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hKC : K.pCoreIn 2 ≤ C := le_inf ((pCoreIn_le 2 K).trans inf_le_left) hk
  apply le_antisymm
  · exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hKC
      (hCK.trans (K.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K))))).trans
      (pCoreIn_mono_of_normalizes inf_le_left hJC)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
      (le_inf (pCoreIn_le 2 J) (hQ.trans hc))
      (inf_le_left.trans (J.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

end CFSG.Quasithin.Chapter8.MathieuShadowRows
