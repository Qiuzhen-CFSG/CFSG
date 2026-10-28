module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.EscapeGeneration
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Original
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Positive generation for the original exchanged-component parabolic

The original nonnormal C-component has a simple nonnormal image in the
literal quotient H/J. The genuine two-factor argument supplies a positive
E-generation witness there without a model or rank-bound input. Since J is
the full solvable maximal core, the normal solvable-kernel theorem lifts that
witness to H. This is the paired input for minimal-parabolic attainment.

Source: Aschbacher–Smith E.1.10–11 and E.2.2, printed pp.212–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem paired_star_exists_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f (H ⧸ ChapterB.minimalParabolicCore T hP) := by
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
  exact Paired.coreFree_exists_isEGenerated (source_star_sqtk hA hH T hP hs).stronglyQuasithin
    S hPs hsX hJs L hi.2.1 hi.2.2.2 hLn

theorem paired_exists_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    ∃ f : ℕ, 0 < f ∧ IsEGenerated f H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  obtain ⟨f,hf,hfG⟩ := paired_star_exists_isEGenerated hA hH T hP hs K hK hgen hn
  exact ⟨f,hf,IsEGenerated.of_normal_solvable_subgroup hf J hfG⟩

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
