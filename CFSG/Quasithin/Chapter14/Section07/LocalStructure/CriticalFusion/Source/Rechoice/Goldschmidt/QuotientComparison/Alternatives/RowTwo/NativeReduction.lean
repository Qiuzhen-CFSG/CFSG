module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo.Transport
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication

/-!
# Recovering the native marked extraspecial row

A normal extraspecial subgroup of order 27 forces a noncyclic three-core.
The original I is the full known-simple SQTK cover of its bang quotient,
and the genuine bang Goldschmidt triple is already proved in Preparation.
The common Sylow has order different from two. Thus marked F.6.16 applies;
the elementary-nine model has the wrong order, leaving the exact Heisenberg
extension with its prescribed E₄ action and both local residual markings.

Only the earlier universal Goldschmidt rigidity and section-centralizer
implications remain explicit here. The input extension is never identified
with an arbitrary semidirect product, and the plus and bang quotients remain
distinct. The subnormal-S₃ obstruction in this fixed model is separate.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
F.6.16, printed pp.308–309; Lemma 14.7.70, printed p.1075.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
open Representation Chapter12.Section08 MarkedCubicRecognition
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

private theorem noncyclic_core_of_extraspecial
    {D : Type*} [Group D] [Finite D] (N : Subgroup D) [N.Normal]
    (hex : IsExtraspecial 3 N) (hc : Nat.card N = 27) : ¬ IsCyclic (pCore 3 D) := by
  intro hcyc
  let := hcyc
  let := hex
  have hle : N ≤ pCore 3 D := le_sSup ⟨inferInstance, IsExtraspecial.isPGroup 3 N⟩
  let : IsCyclic N := isCyclic_of_injective (inclusion hle) (inclusion_injective hle)
  have h := IsExtraspecial.center_order_p 3 N
  rw [center_eq_top, card_top, hc] at h
  norm_num at h

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- Recover the native marked action from the genuine triple and SQTK cover.
The unmarked extraspecial row alone is not used as an action specification. -/
theorem extraspecial_marked_model
    (rigidity : ChapterF.Noncyclic.GoldschmidtRigidityInput.{u})
    (centralizers : ChapterF.Noncyclic.SectionCentralizerInput.{u,u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c)
    (N : Subgroup ((I c) ⧸ pPrimeCore 3 (I c))) [N.Normal]
    (hex : IsExtraspecial 3 N) (hcard : Nat.card N = 27)
    (eQ : (((I c) ⧸ pPrimeCore 3 (I c)) ⧸ N) ≃* FSource.E4) :
    Nonempty (ChapterF.Noncyclic.MarkedRecognition.MarkedModel
      (bang c (group F L)) (bang c (YT c)) (HeisenbergPrime 3)
      heisenbergAction leftAxis.range rightAxis.range) := by
  have ht := bang_triple d c h k small
  have hn := noncyclic_core_of_extraspecial N hex hcard
  have hnot : ¬ Nonempty ((bang c (group F L) ⊓ bang c (YT c) : Subgroup _) ≃* C2) := by
    rintro ⟨e⟩
    obtain ⟨S, hS⟩ := ht.intersection_sylow
    have hS2 : Nat.card S = 2 := by
      rw [← hS, Nat.card_congr e.toEquiv]
      simp [C2]
    exact bang_sylow_card_ne_two d c h k small
      ((Nat.card_congr ((bangSylow c).equiv S).toEquiv).trans hS2)
  have models := ChapterF.Noncyclic.source_marked_models_of_inputs rigidity centralizers
    (Geometry.local_and_sqtk (d := d) (c := c) k.nontrivial).2 (MulEquiv.refl _)
    ht hn hnot
  rcases models with hm | hm
  · obtain ⟨m⟩ := hm
    have e := m.ambientEquiv.symm.trans nineExtension_equiv_symmetric_product.some
    have hc : Nat.card ((I c) ⧸ pPrimeCore 3 (I c)) = 36 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    have hc' : Nat.card ((I c) ⧸ pPrimeCore 3 (I c)) = 108 := by
      rw [card_eq_card_quotient_mul_card_subgroup N, hcard, Nat.card_congr eQ.toEquiv]
      norm_num [FSource.E4, FSource.C]
    omega
  · exact hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.RowTwo
