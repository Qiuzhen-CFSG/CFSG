module

public import Stellmacher.ElementaryAbelianMaxSylowImages
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# The literal relative image family inside a Sylow image

A conjugate of a local maximal elementary subgroup is globally maximal.
Kernel conjugacy localizes it back into the chosen Sylow without changing
its image. Thus the relative image family restricted to that Sylow image
is exactly the original local image family, and generates the image of J(R).
This is a statement about the individual generators, not an interchange of
intersection and subgroup generation.

Source: Aschbacher–Smith B.2.7–9, printed pp.76–77, used in 13.6.22, p.932.
-/

public section
open Subgroup Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
variable {H Q : Type*} [Group H] [Finite H] [Group Q] [Finite Q]

omit [Finite Q] in
/-- Restricting the conjugate image family recovers exactly the local image family. -/
theorem relativeMaxOffenderImages_sylow_iff
    (R : Sylow 2 H) (V : Subgroup H) (q : H →* Q) (hq : Function.Surjective q)
    (E : Subgroup Q) :
    E ∈ relativeMaxOffenderImages R V q ∧ E ≤ (R : Subgroup H).map q ↔
      E ∈ maxOffenderImages R V q := by
  constructor
  · rintro ⟨⟨A, hA, h, rfl, hne⟩, hER⟩
    obtain ⟨x, rfl⟩ := hq h
    have hAg := (maxFamily_sylow_iff R A).mp hA |>.2
    have hD := (maxFamily_map_injective_iff (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective ⊤ A).mpr hAg
    rw [map_top_of_surjective _ (MulAut.conj x).surjective] at hD
    have hm : (A.map (MulAut.conj x).toMonoidHom).map q =
        (A.map q).map (MulAut.conj (q x)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext a
      simp [MulAut.conj_apply]
    obtain ⟨B, hB, hBe⟩ := exists_maxFamily_sylow_same_image R q _ hD (hm ▸ hER)
    exact ⟨B, hB, hBe.trans hm, hne⟩
  · rintro ⟨A, hA, rfl, hne⟩
    refine ⟨⟨A, hA, 1, ?_, hne⟩, map_mono hA.1⟩
    change (A.map q).conjBy 1 = A.map q
    exact Subgroup.conjBy_one _

/-- The restricted relative family generates precisely the actual Thompson image. -/
theorem relativeMaxOffenderImages_sylow_generated
    (R : Sylow 2 H) (V : Subgroup H) (q : H →* Q) (hq : Function.Surjective q) :
    (elementaryAbelianMaxJ (R : Subgroup H)).map q =
      generatedBy (relativeMaxOffenderImages R V q) ((R : Subgroup H).map q) := by
  rw [maxOffenderImages_generated R V q]
  apply le_antisymm
  · apply iSup_le
    intro E
    apply iSup_le
    rintro ⟨hE, _⟩
    exact le_iSup_of_le E (le_iSup_of_le
      ((relativeMaxOffenderImages_sylow_iff R V q hq E).mpr hE) le_rfl)
  · apply iSup_le
    intro E
    apply iSup_le
    intro hE
    exact le_iSup_of_le E (le_iSup_of_le
      ⟨(relativeMaxOffenderImages_sylow_iff R V q hq E).mp hE, le_top⟩ le_rfl)
end CFSG.Quasithin.ChapterB
