module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo.NativeReduction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo.ProductModel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo.HeisenbergModel

/-!
# Elimination of F.6.18 row (2) in 14.7.70

The literal small subnormal witness reduces to S₃ in either row-(2) model.
In the product case, normality of that fixed model's subnormal S₃ subgroups
lifts to the original plus quotient and contradicts the proved local residual
centralization obstruction. In the extraspecial case, native marked F.6.16
recovers the prescribed Heisenberg–E₄ extension from the actual SQTK cover.

`not_rowTwo` assembles the two proved model exclusions on the original
quotients. Its only earlier-source parameters are the universal F.6.13 and
A.1.31(1) implications, owned by qt-f06-rigidity and
qt-a-01-cyclic-centralizer-sections. Their final source discharge remains with
qt-f06-noncyclic and the comparison assembly. No finite-model premise or
ambient quotient identification is assumed. The earlier conditional API is
preserved below.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed pp.1074–1075; F.6.16 and F.6.18, printed pp.308–310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
open Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- Conditional final comparison, with its two concrete finite-model obligations
visible. These obligations are not assertions about the source quotients. -/
theorem not_rowTwo_of_model_facts
    (productNormal : ∀ K : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      K.IsSubnormal → Nonempty (K ≃* Equiv.Perm (Fin 3)) → K.Normal)
    (nativeObstruction : ∀ K : Subgroup MarkedCubicRecognition.HeisenbergExtension,
      K.IsSubnormal → Nonempty (K ≃* Equiv.Perm (Fin 3)) → False)
    (rigidity : ChapterF.Noncyclic.GoldschmidtRigidityInput.{u})
    (centralizers : ChapterF.Noncyclic.SectionCentralizerInput.{u,u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    ¬ RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) := by
  intro row
  obtain ⟨K, hK, ⟨eK⟩⟩ := rowTwo_small_symmetricThree c k small row
  obtain ⟨himage, ⟨eimage⟩⟩ := comparisonMap_small_image c k K hK eK
  unfold RowTwoModel at row
  rcases row with hp | hn
  · obtain ⟨e⟩ := hp
    let J := K.map (comparisonMap c)
    let H := J.map e.toMonoidHom
    let : H.Normal := productNormal H (himage.map e.surjective)
      ⟨(e.subgroupMap J).symm.trans eimage⟩
    have he : H.comap e.toMonoidHom = J := by
      change (J.map e.toMonoidHom).comap e.toMonoidHom = J
      rw [comap_map_eq, e.toMonoidHom.ker_eq_bot e.injective, sup_bot_eq]
    let : J.Normal := by rw [← he]; infer_instance
    let : K.Normal := comparisonMap_normal_lift c k K hK eK
    exact no_normal_symmetricThree d c h k K eK
  · obtain ⟨N, hN, hex, hc, _, ⟨eQ⟩⟩ := hn
    let := hN
    obtain ⟨m⟩ := extraspecial_marked_model d c rigidity centralizers h k small N hex hc eQ
    let e := m.ambientEquiv.symm
    exact nativeObstruction ((K.map (comparisonMap c)).map e.toMonoidHom)
      (himage.map e.surjective)
      ⟨(e.subgroupMap (K.map (comparisonMap c))).symm.trans eimage⟩

/-- F.6.18 row (2) is impossible in the literal 14.7.70 comparison. Both
finite-model facts are discharged; only the stated earlier universal source
implications remain explicit. -/
theorem not_rowTwo
    (rigidity : ChapterF.Noncyclic.GoldschmidtRigidityInput.{u})
    (centralizers : ChapterF.Noncyclic.SectionCentralizerInput.{u,u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    ¬ RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) := by
  rintro (hp | ⟨N, hN, hex, hcard, hexp, ⟨eQ⟩⟩)
  · exact not_product_rowTwo d c h k small hp
  · let := hN
    exact not_extraspecial_row d c rigidity centralizers h k small N hex hcard hexp eQ

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
