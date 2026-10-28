module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddTwo
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The original normal odd PSL₂ row in the E.6 numerical dispatcher

The actual marked image is K* in H/core_H(M). The completed generation
calculation includes all odd defining fields above five permitted by SQTK,
with their full outer action. In particular it applies to the original
SingleOddLinearModel row: its congruence excludes the remaining degree-five
case, and its stored field and group equivalence give the literal model.
Rank-one E-generation lifts through the full solvable core and bounds n(H).

Source: Aschbacher–Smith E.2.2(2c), pp.215–216, and E.6.27, p.257.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}
/-- The raw odd PSL₂ source model retains the original quotient map. -/
theorem normal_odd_two_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {q : ℕ} (ho : Odd q) (hq : 5 < q)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 q) :
    IsEGenerated 1 H :=
  Structure.NumericalBounds.normal_odd_two_isEGenerated hA hH T hP hs K hK hgen ho hq hm

/-- The raw normal odd PSL₂ row has generation parameter at most one. -/
theorem normal_odd_two_parameter_le_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {q : ℕ} (ho : Odd q) (hq : 5 < q)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 q) :
    generationParameter H ≤ 1 :=
  Structure.NumericalBounds.normal_odd_two_upper hA hH T hP hs K hK hgen ho hq hm

/-- The raw odd PSL₂ row is absent from the original n(H)>1 dispatcher. -/
theorem normal_odd_two_false_of_parameter_gt_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {q : ℕ} (ho : Odd q) (hq : 5 < q)
    (hm : ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 q)
    (hn : 1 < generationParameter H) : False :=
  (Nat.not_le_of_gt hn) (normal_odd_two_parameter_le_one hA hH T hP hs K hK hgen ho hq hm)

/-- E.2.2(2c)'s literal stored field and component marking give generation of H. -/
theorem single_odd_linear_isEGenerated
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H)) :
    IsEGenerated 1 H := by
  obtain ⟨p,d,hp,hp3,hd,hd2,hmod,F,_,_,hF,e,_,_,_⟩ := hm
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hq : 5 < p^d := by
    rcases (show d=1 ∨ d=2 by omega) with hd | hd
    · subst d
      simp only [pow_one] at hmod ⊢
      omega
    · subst d
      nlinarith
  exact normal_odd_two_isEGenerated hA hH T hP hs K hK hgen (ho.pow) hq
    ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩

/-- The complete SingleOddLinearModel row has n(H)≤1 through the full core. -/
theorem single_odd_linear_parameter_le_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H)) :
    generationParameter H ≤ 1 :=
  generationParameter_le (by decide) (single_odd_linear_isEGenerated hA hH T hP hs K hK hgen hm)

/-- The original source dispatcher excludes E.2.2(2c) when n(H)>1. -/
theorem single_odd_linear_false_of_parameter_gt_one
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H))
    (hn : 1 < generationParameter H) : False :=
  (Nat.not_le_of_gt hn) (single_odd_linear_parameter_le_one hA hH T hP hs K hK hgen hm)
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
