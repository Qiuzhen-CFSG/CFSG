module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.Complete
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Original normal odd PSL₂ numerical bounds

The original normal component has nonabelian simple image in the literal
quotient H/J, where J is the full core of the unique maximal Sylow overgroup.
That image equals F*(H/J). Its SQTK property and Sylow supplement allow the
complete odd PSL₂ generation theorem to apply, including field extensions.
Positive-rank E-generation lifts through the actual solvable J; hence n(H)≤1.
No equality of generation parameters across J is used.

Source: Aschbacher–Smith E.1.14(6) and E.2.2(2c), pp.214–216.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
/-- Rank-one E-generation on the original odd PSL₂ normal-component source,
with its full solvable core retained. -/
theorem normal_odd_two_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {q : ℕ} (ho : Odd q) (hq : 5 < q)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 q) :
    IsEGenerated 1 H := by
  let J := ChapterB.minimalParabolicCore T hP
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map (QuotientGroup.mk' J)
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  apply IsEGenerated.of_normal_solvable_subgroup (by decide) J
  obtain ⟨hLs,hLa,hLn,hLT⟩ := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hstar := source_star_minimal_core_free T hP
  have hF : generalizedFitting (H ⧸ J) = L :=
    (Sporadic.faithful_normal_structure S hstar.1 hstar.2 L hLa hLT).1
  let : IsSimpleGroup (generalizedFitting (H ⧸ J)) := hF ▸ hLs
  have hmodel : ClassicalGroup.IsPSL (generalizedFitting (H ⧸ J)) 2 q := hF ▸ hm
  exact ValuesOdd.PSLTwoGeneration.isEGenerated_one_of_model
    (source_star_sqtk hA hH T hP hs) S (hF ▸ hLT) ho hq hmodel

/-- The upper bound follows from actual generation of H, without comparing
parameters across its maximal core. -/
theorem normal_odd_two_upper
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {q : ℕ} (ho : Odd q) (hq : 5 < q)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 q) :
    generationParameter H ≤ 1 :=
  generationParameter_le (by decide)
    (normal_odd_two_isEGenerated hA hH T hP hs K hK hgen ho hq hm)
end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
