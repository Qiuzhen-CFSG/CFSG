module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The normal odd-degree-three exclusion in the original E.6 dispatcher

The original marked image is K* in H/core_H(M). Both its linear and unitary
odd-prime models supply actual rank-one E-generation of H and n(H)≤1.
Thus neither normal odd-degree-three row can occur when the original E.6
parameter exceeds one. The kernel, component, source model and Sylow are
unchanged; no numerical equality between H and its star quotient is used.

Source: Aschbacher–Smith E.2.2, pp.215–216, and E.6.27, p.257.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
/-- The original marked normal odd-degree-three row supplies rank-one E-generation. -/
theorem normal_odd_three_isEGenerated
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p ∨
      ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p) :
    IsEGenerated 1 H :=
  Structure.NumericalBounds.normal_odd_three_isEGenerated hA hH T hP hs K hK hgen hp ho hm

/-- Numerical elimination of both normal odd degree-three rows in E.6. -/
theorem normal_odd_three_parameter_le_one
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p ∨
      ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p) :
    generationParameter H≤1 :=
  Structure.NumericalBounds.normal_odd_three_upper hA hH T hP hs K hK hgen hp ho hm

/-- The literal E.6 dispatcher cannot select a normal odd-degree-three image
when the original generation parameter exceeds one. -/
theorem normal_odd_three_false_of_parameter_gt_one
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p ∨
      ClassicalGroup.IsPSU (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 p)
    (hn:1<generationParameter H) : False :=
  (Nat.not_le_of_gt hn) (normal_odd_three_parameter_le_one hA hH T hP hs K hK hgen hp ho hm)
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
