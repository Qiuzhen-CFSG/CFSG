module
public import CFSG.Quasithin.ChapterE.Section02.Structure.OddDegreeThree.Linear
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.FourActors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.PrimeCentralizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry
/-!
# Rank-one E-generation in the normal odd linear source row

The genuine E.2.2 source forces the field prime to be three modulo four
and supplies the full graph-extension marking. The field-three graph model
is already generated. Above three, the inner-family and outer-four proofs
combine with the prime-field outer-eight calculation. The source congruence
excludes the separate prime-five local geometry entirely. All original
families, local tau and quotient-rank conventions are retained.

Source: Aschbacher–Smith E.1.14(7) and E.2.2(2d), pp.214–216.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.OddThree
open ValuesOdd.PSLThreeGeneration.ProperExtension
open GraphLarge GraphLarge.OuterFamilies ValuesOdd.PSLTwoGeneration.PrimeGeometry
private theorem graph_generated (F:Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:p%4=3) (hF:Nat.card F=p)
    (hs:IsStronglyQuasithin (graphExtension F)) : IsEGenerated 1 (graphExtension F) := by
  let : Finite (GorensteinWalter.PGL2 F):=Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  by_cases he:p=3
  · exact GraphThree.graphExtension_isEGenerated_one_of_three (he ▸ hF)
  have hbig:5<p := by omega
  apply isEGenerated_one_of_outer_families F hp ho (by omega) hF hs
  intro T Ω hΩ hlarge houter M hTM hM hN
  apply familyEscapes_of_positioned_outer_cases F hp ho hF T Ω hΩ hlarge houter M hM hN
  · intro A hA hAT hfour hinner z hz hzL hzA hTz
    exact familyEscapes_of_positioned_four_actor F hp ho (by omega) hF
      T Ω hΩ hlarge houter M hTM hM hN A hA hAT hfour hinner z hz hzL hzA hTz
  · intro A hA hAT hcard hfour z hz hzL hzA hTz
    exact EightActors.familyEscapes_of_positioned_eight_actor_of_prime_geometry F hp ho hbig hF
      (Inner.concreteLocalGeometryAt_of_prime_field hp ho hbig hF (MulEquiv.refl _))
      (Diagonal.concreteLocalGeometryAt_of_prime_field hp ho hbig hF (MulEquiv.refl _))
      (fun hmod=>InnerGenerationGeometry.fourGroupOddMixing_of_card_mod_four_eq_three F hp (by omega) hF hmod)
      T Ω hΩ hlarge houter M hTM hM hN A hA hAT hcard hfour z hz hzL hzA hTz

/-- The actual normal odd linear E.2.2 row is rank-one E-generated. -/
theorem linear_isEGenerated {H:Type*} [Group H] [Finite H]
    (hH:IsStronglyQuasithin H) (T:Sylow 2 H) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (K:Subgroup H) [K.Normal] [IsSimpleGroup K]
    (hgen:K⊔(T:Subgroup H)=⊤) (hcore:pCore 2 H=⊥)
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hm:ClassicalGroup.IsPSL K 3 p) : IsEGenerated 1 H := by
  have hmod:=OddDegreeThree.linear_congruence T hP K hgen hcore hp ho hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
  let : IsSimpleGroup PSL(3,F):=e.symm.isSimpleGroup
  obtain ⟨f,_⟩:=OddDegreeThree.linear_graph_extension T hP K hgen hcore hp ho hF e
  have hs:IsStronglyQuasithin (graphExtension F) := by
    intro r hr hro
    exact (Theory.GroupTheory.primeRank_le_of_injective r f.symm.toMonoidHom f.symm.injective).trans (hH r hr hro)
  exact (graph_generated F hp ho hmod hF hs).map_equiv f.symm
end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.OddThree
