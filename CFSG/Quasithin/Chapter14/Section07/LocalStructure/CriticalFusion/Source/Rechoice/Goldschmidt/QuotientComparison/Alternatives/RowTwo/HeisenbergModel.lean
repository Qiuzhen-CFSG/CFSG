module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo.NativeReduction
public import Theory.GroupAction.MarkedCubicRecognition.SubnormalObstruction

/-!
# The extraspecial row obstruction in 14.7.70

The literal small subnormal witness in the plus quotient is S₃ by the
row-order calculation. Its image under the actual comparison map is again
a subnormal S₃. Native marked F.6.16 supplies an ambient equivalence with
the prescribed Heisenberg–E₄ extension, where the model obstruction applies.

Only the earlier universal Goldschmidt rigidity and section-centralizer
implications remain explicit. Their producers are qt-f06-rigidity and
qt-a-01-cyclic-centralizer-sections; their final discharge belongs to the
source assembly. Neither normality of the witness nor a model classifier
is assumed.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed p.1075, and F.6.16, printed pp.308–309.
-/

public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
open Representation Chapter12.Section08
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- Eliminate the literal extraspecial clause of row (2), using its native
marked action recovered from the genuine source geometry. -/
theorem not_extraspecial_row
    (rigidity : ChapterF.Noncyclic.GoldschmidtRigidityInput.{u})
    (centralizers : ChapterF.Noncyclic.SectionCentralizerInput.{u,u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c)
    (N : Subgroup ((I c) ⧸ pPrimeCore 3 (I c))) [N.Normal]
    (hex : IsExtraspecial 3 N) (hcard : Nat.card N = 27)
    (hexp : Monoid.exponent N = 3)
    (eQ : (((I c) ⧸ pPrimeCore 3 (I c)) ⧸ N) ≃* FSource.E4) : False := by
  have row : RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) :=
    Or.inr ⟨N, inferInstance, hex, hcard, hexp, ⟨eQ⟩⟩
  obtain ⟨K, hK, ⟨eK⟩⟩ := rowTwo_small_symmetricThree c k small row
  obtain ⟨himage, ⟨eimage⟩⟩ := comparisonMap_small_image c k K hK eK
  obtain ⟨m⟩ := extraspecial_marked_model d c rigidity centralizers h k small N hex hcard eQ
  let e := m.ambientEquiv.symm
  exact MarkedCubicRecognition.SubnormalObstruction.no_subnormal_symmetricThree
    ((K.map (comparisonMap c)).map e.toMonoidHom) (himage.map e.surjective)
    ⟨(e.subgroupMap (K.map (comparisonMap c))).symm.trans eimage⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
