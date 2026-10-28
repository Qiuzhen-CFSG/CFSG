module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Paired.Attainment
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original paired odd-prime source bound at two

The actual simple component in H/J has the proved prime-field automorphism
rank bound. Its paired E-generation theorem supplies degree two. Generation
lifts through the full solvable maximal core J, so the original H has
n(H) at most two. No equality of parameters across J is asserted.
Source: Aschbacher–Smith E.1.10 and paired E.2.2, pp.212–216.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
theorem paired_prime_isEGenerated_two
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p) :
    IsEGenerated 2 H := by
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
  apply IsEGenerated.of_normal_solvable_subgroup (by decide) J
  exact Paired.coreFree_prime_linear_isEGenerated_two
    (source_star_sqtk hA hH T hP hs).stronglyQuasithin S hPs hsX hJs L hi.2.1 hi.2.2.2 hLn hp hm

theorem paired_prime_parameter_le_two
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p) :
    generationParameter H ≤ 2 :=
  generationParameter_le (by decide) (paired_prime_isEGenerated_two hA hH T hP hs K hK hgen hn hp hm)
end CFSG.Quasithin.ChapterE.Structure.NumericalBounds

