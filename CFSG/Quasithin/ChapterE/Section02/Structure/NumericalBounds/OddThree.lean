module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NumericalBounds.OddThree.Linear
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Complete
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Original normal odd-degree-three numerical bounds

The actual star image of the original normal C-component is simple and is
F*(H/J), with its inherited SQTK condition and prescribed Sylow supplement.
The linear source congruence and literal graph model give rank-one generation;
the completed unitary family supplies it in every odd prime case. The full
maximal core J is solvable, so positive-rank E-generation lifts from H/J to H.
The resulting witness bounds n(H) by one without any equality across J.

Source: Aschbacher–Smith E.1.10–14 and E.2.2(2d), pp.212–216.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds
universe u
variable {H:Type u} [Group H] [Finite H] {κ:GroupClass.{u}}
/-- Generation on the actual odd degree-three normal-component source. -/
theorem normal_odd_three_isEGenerated
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p ∨
      ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p) :
    IsEGenerated 1 H := by
  let J:=ChapterB.minimalParabolicCore T hP
  let q:=QuotientGroup.mk' J
  let S:=T.mapSurjective (QuotientGroup.mk'_surjective J)
  let L:=K.map q
  let : Group.IsSolvable J:=ChapterB.minimalParabolic_core_solvable T hP
  apply IsEGenerated.of_normal_solvable_subgroup (by decide) J
  obtain ⟨hLs,hLa,hLn,hLT⟩:=source_normal_simple_image T hP hs K hK hgen
  let : IsSimpleGroup L:=hLs
  let : L.Normal:=hLn
  have hstar:=source_star_minimal_core_free T hP
  have hcore:pCore 2 (H ⧸ J)=⊥:=le_bot_iff.mp
    ((ChapterB.minimalParabolicTwoCore_le_core S hstar.1).trans hstar.2.le)
  have hG:=source_star_sqtk hA hH T hP hs
  rcases hm with hm|hm
  · exact OddThree.linear_isEGenerated hG.stronglyQuasithin S hstar.1 L hLT hcore hp ho hm
  · have hF:generalizedFitting (H ⧸ J)=L :=
      (Sporadic.faithful_normal_structure S hstar.1 hstar.2 L hLa hLT).1
    let : IsSimpleGroup (generalizedFitting (H ⧸ J)):=hF ▸ hLs
    have hmodel:ClassicalGroup.IsPSU (generalizedFitting (H ⧸ J)) 3 p:=hF ▸ hm
    exact ValuesOdd.PSUThreeGeneration.isEGenerated_one_of_model hG S (hF ▸ hLT) hp ho hmodel

/-- The bound is lifted through the full solvable J; no equality of parameters
across J is asserted. -/
theorem normal_odd_three_upper
    (hA:ChapterA.Section02.TheoremA κ H) (hH:IsSQTK κ H)
    (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (hs:¬Group.IsSolvable H) (K:Subgroup H) (hK:K.IsCComponent) [K.Normal]
    (hgen:K⊔(T:Subgroup H)=⊤) {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p ∨
      ClassicalGroup.IsPSU (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p) :
    generationParameter H≤1 :=
  generationParameter_le (by decide) (normal_odd_three_isEGenerated hA hH T hP hs K hK hgen hp ho hm)
end CFSG.Quasithin.ChapterE.Structure.NumericalBounds
