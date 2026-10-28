module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion.Carrier
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion.Census
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Coordinates

/-!
# Exhaustive ambient fusion of elementary eights in the fixed Sylow

The faithful 64-coordinate parametrization identifies every input subgroup
with one of the eight full coordinate lists. Explicit determinant-one matrices
then send the whole subgroup either to the original actor or to the published
second representative. All conjugation takes place in the literal graph
extension; no inner intersection is substituted for the original actor.

This is the finite fusion input of the reselection argument supporting
Aschbacher--Smith E.1.14(7), printed p.214. The independent radical-quotient
position calculation remains with the parent reselection assembly.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection
open FiveSourceAudit Fusion

private theorem conjugation_back {G : Type*} [Group G] (A B : Subgroup G) (g : G)
    (h : A.map (MulAut.conj g).toMonoidHom = B) :
    A = B.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hb := (map_symm_eq_iff_map_eq (K := A) (H := B) (e := MulAut.conj g)).mpr h
  have he : ((MulAut.conj g).symm : G →* G) = (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    change g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹
    rw [inv_inv]
  rw [← he]
  exact hb.symm

/-- The exact finite census contract feeds the published ambient fusion
contract, with all coordinate transport and conjugators discharged. -/
theorem standardFusion_of_census (hcensus : Census) : StandardFusion := by
  intro A hA hAS hcard
  obtain ⟨i,rfl⟩ := candidate_of_census hcensus A hA hAS hcard
  have he := candidate_conjugate i
  simp only [target] at he
  split_ifs at he
  · rw [candidate_five] at he
    exact Or.inl ⟨(innerSL (witness i))⁻¹,
      conjugation_back (candidate i) actor (innerSL (witness i)) he⟩
  · rw [candidate_four] at he
    exact Or.inr ⟨innerSL (witness i), he⟩

/-- Every elementary abelian subgroup of order eight in the literal fixed
Sylow belongs to the original family or is ambient-conjugate to the published
second representative. All finite coverage and fusion premises are discharged. -/
theorem standardFusion : StandardFusion := standardFusion_of_census Fusion.census

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.OuterReselection
