module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Generation
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Original paired binary generation and parameter upper bounds

The literal star image of a nonnormal C-component is simple, remains
nonnormal, and generates H/J with the prescribed quotient Sylow. The genuine
paired PSL₂ or Suzuki generation theorem applies to this exact image.
Generation lifts through the full solvable maximal core J, including any
odd central part, giving both an attained witness and n(H) ≤ f.
No parameter equality across J is asserted.

Source: Aschbacher–Smith E.1.10–14 and E.2.2, printed pp.212–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem paired_bender_star_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) {f : ℕ}
    (hm : (2 ≤ f ∧ ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) ∨
      ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
        ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    IsEGenerated f (H ⧸ ChapterB.minimalParabolicCore T hP) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsX : ¬ Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := source_component_simple_image T hP hs K hK hgen
  have hLn : ¬ L.Normal := fun hd => hn (cComponent_normal_of_quotient_normal hK J hd)
  obtain ⟨hPs,hJs⟩ := source_star_minimal_core_free T hP
  have hGX := (source_star_sqtk hA hH T hP hs).stronglyQuasithin
  rcases hm with ⟨hf,hm⟩ | ⟨m,hm,rfl,⟨e⟩⟩
  · exact Paired.coreFree_linear_isEGenerated hGX S hPs hsX hJs L hi.2.1 hi.2.2.2 hLn hf hm
  · exact Paired.coreFree_suzuki_isEGenerated hGX S hPs hsX hJs L hi.2.1 hi.2.2.2 hLn hm e

theorem paired_bender_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) {f : ℕ}
    (hm : (2 ≤ f ∧ ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) ∨
      ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
        ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : IsEGenerated f H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hf : 0 < f := by rcases hm with h | ⟨m,hm,he,_⟩ <;> omega
  exact IsEGenerated.of_normal_solvable_subgroup hf J
    (paired_bender_star_isEGenerated hA hH T hP hs K hK hgen hn hm)

theorem paired_bender_upper
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) {f : ℕ}
    (hm : (2 ≤ f ∧ ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) ∨
      ∃ m : ℕ, 0 < m ∧ f = 2*m+1 ∧ Nonempty
        ((K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) : generationParameter H ≤ f := by
  have hf : 0 < f := by rcases hm with h | ⟨m,hm,he,_⟩ <;> omega
  exact generationParameter_le hf (paired_bender_isEGenerated hA hH T hP hs K hK hgen hn hm)

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
