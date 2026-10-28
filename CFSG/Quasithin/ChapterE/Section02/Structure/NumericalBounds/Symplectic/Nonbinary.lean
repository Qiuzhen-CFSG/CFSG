module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.NonbinaryExtension
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.Classical
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Original nonbinary symplectic generation bounds

For a normal C-component, its actual image K* in H/J is simple and equals
F*(H/J). The full symplectic extension theorem gives E-generation at the
marked field exponent, including diagram actors. B.6.8 proves the original
maximal core J solvable, so generation lifts through its entire kernel.
This proves n(H) ≤ f without asserting equality of parameters across J.

Source: Aschbacher–Smith E.1.10–14 and E.2.2, printed pp.212–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The actual symplectic star quotient is E-generated at its field exponent. -/
theorem normal_symplectic_star_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) :
    IsEGenerated f (H ⧸ ChapterB.minimalParabolicCore T hP) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L := K.map q
  obtain ⟨hLs,hLa,hLn,hLT⟩ := source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L := hLs
  let : L.Normal := hLn
  have hstar := source_star_minimal_core_free T hP
  have hF := (Sporadic.faithful_normal_structure S hstar.1 hstar.2 L hLa hLT).1
  let : IsSimpleGroup (generalizedFitting (H ⧸ J)) := by rw [hF]; infer_instance
  apply ValuesEvenClassical.RankTwoUpper.SymplecticFour.isEGenerated_of_isPSp
    (source_star_sqtk hA hH T hP hs) hf S
  · rw [hF]
    exact hLT
  · rw [hF]
    exact hm

/-- E-generation lifts through the full original solvable maximal core. -/
theorem normal_symplectic_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) :
    IsEGenerated f H := by
  let J := ChapterB.minimalParabolicCore T hP
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  exact IsEGenerated.of_normal_solvable_subgroup (by omega) J
    (normal_symplectic_star_isEGenerated hA hH T hP hs K hK hgen hf hm)

/-- The source-correct parameter upper bound in the normal symplectic row. -/
theorem normal_symplectic_upper
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSp
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 (2^f)) :
    generationParameter H ≤ f :=
  generationParameter_le (by omega)
    (normal_symplectic_isEGenerated hA hH T hP hs K hK hgen hf hm)

end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
