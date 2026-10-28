module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo.Transport
public import Theory.SpecificGroups.SymmetricThree.SubnormalProduct

/-!
# Excluding the product model in F.6.18 row (2)

The literal product alternative is incompatible with the source small
subnormal witness.  Transport embeds its S₃ image into the bang quotient;
after identifying that quotient with `S₃ × S₃`, the concrete subnormal-product
lemma makes the image normal.  `comparisonMap_normal_lift` then lifts this
normality back to the plus quotient, where the established local residual
contradiction applies.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed pp.1074--1075 (PDF pp.1091--1092).
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

/-- The product shape in row (2) is impossible for the literal source quotients. -/
theorem not_product_rowTwo (h : Geometry d c) (k : CoreFacts c)
    (small : SmallSubnormal c) :
    ¬ Nonempty (((I c) ⧸ pPrimeCore 3 (I c)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rintro ⟨e⟩
  let row : RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) := Or.inl ⟨e⟩
  obtain ⟨K, hK, ⟨eK⟩⟩ := rowTwo_small_symmetricThree c k small row
  obtain ⟨himage, ⟨eimage⟩⟩ := comparisonMap_small_image c k K hK eK
  let J := K.map (comparisonMap c)
  let H := J.map e.toMonoidHom
  have eH : H ≃* Equiv.Perm (Fin 3) := by
    change J.map e.toMonoidHom ≃* Equiv.Perm (Fin 3)
    exact (e.subgroupMap J).symm.trans eimage
  let : H.Normal := SymmetricThreeProduct.subnormal_symmetricThree_normal H
    (himage.map e.surjective)
    ⟨eH⟩
  have he : H.comap e.toMonoidHom = J := by
    change (J.map e.toMonoidHom).comap e.toMonoidHom = J
    rw [comap_map_eq, e.toMonoidHom.ker_eq_bot e.injective, sup_bot_eq]
  let : J.Normal := by rw [← he]; infer_instance
  let : K.Normal := comparisonMap_normal_lift c k K hK eK
  exact no_normal_symmetricThree d c h k K eK

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
