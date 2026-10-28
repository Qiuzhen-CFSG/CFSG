module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.PrimeSharp.Generation
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Sharp paired prime generation through the full original core

The actual nonnormal C-component has a simple nonnormal image under the
literal map H→H/J, where J is the unique maximal core. Its prescribed quotient
Sylow satisfies genuine core-free minimality. Sharp prime generation applies
to this same image, and generation lifts through the whole solvable J,
including its possible odd central part. Both the attained IsEGenerated 1 H
witness and n(H)≤1 are retained; no quotient-parameter equality is asserted.
The odd model starts at p≥7; p=5 remains the binary field-four row.
Source: Aschbacher–Smith E.1.10–11 and E.2.2, printed pp.212–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

theorem paired_prime_star_isEGenerated_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p) :
    IsEGenerated 1 (H ⧸ ChapterB.minimalParabolicCore T hP) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  have hsX : ¬Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := source_component_simple_image T hP hs K hK hgen
  have hLn : ¬L.Normal := fun hd => hn (cComponent_normal_of_quotient_normal hK J hd)
  obtain ⟨hPs,hJs⟩ := source_star_minimal_core_free T hP
  exact Paired.PrimeSharp.coreFree_prime_linear_isEGenerated_one
    (source_star_sqtk hA hH T hP hs).stronglyQuasithin S hPs hsX hJs L hi.2.1 hi.2.2.2 hLn hp hm

theorem paired_prime_isEGenerated_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p) :
    IsEGenerated 1 H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  exact IsEGenerated.of_normal_solvable_subgroup (by decide) J
    (paired_prime_star_isEGenerated_one hA hH T hP hs K hK hgen hn hp hm)

theorem paired_prime_upper_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p) :
    generationParameter H ≤ 1 :=
  generationParameter_le (by decide)
    (paired_prime_isEGenerated_one hA hH T hP hs K hK hgen hn hp hm)

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
