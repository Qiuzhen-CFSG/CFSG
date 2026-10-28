module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic

/-!
# Discharging the native noncyclic branch in the source Goldschmidt comparison

The genuine SQTK cover and its actual Goldschmidt triple imply full marked
F.6.16. The extraspecial row therefore carries the prescribed Heisenberg
extension action; its subnormal-S₃ obstruction excludes that row. Combining
the complete row comparison with the original core and B.5 witness removes
F.6.13 rigidity as a premise of the 14.7.70 rank conclusion.

Source: Aschbacher–Smith, proof of 14.7.70, printed pp.1074–1075;
F.6.16, printed pp.308–309, manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.Noncyclic
open Representation Chapter12.Section08 MarkedCubicRecognition
open QuotientComparison QuotientComparison.Alternatives QuotientComparison.Alternatives.RowTwo
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
private theorem extraspecial_marked_model
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
  have models := ChapterF.SourceAssembly.source_marked_models
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


/-- Native F.6.16 excludes row (2) without any rigidity or centralizer
classification premise. The same original plus-to-bang map is retained. -/
theorem not_rowTwo (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    ¬ RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) := by
  intro row
  rcases row with hp | ⟨N,hN,hex,hcard,hexp,⟨eQ⟩⟩
  · exact not_product_rowTwo d c h k small hp
  · let := hN
    have row : RowTwoModel ((I c) ⧸ pPrimeCore 3 (I c)) :=
      Or.inr ⟨N,inferInstance,hex,hcard,hexp,⟨eQ⟩⟩
    obtain ⟨K,hK,⟨eK⟩⟩ := rowTwo_small_symmetricThree c k small row
    obtain ⟨himage,⟨eimage⟩⟩ := comparisonMap_small_image c k K hK eK
    obtain ⟨m⟩ := extraspecial_marked_model d c h k small N hex hcard eQ
    let e := m.ambientEquiv.symm
    exact MarkedCubicRecognition.SubnormalObstruction.no_subnormal_symmetricThree
      ((K.map (comparisonMap c)).map e.toMonoidHom) (himage.map e.surjective)
      ⟨(e.subgroupMap (K.map (comparisonMap c))).symm.trans eimage⟩

/-- The full F.6.18 output gives the actual bang recognition; all of the
noncyclic-row input is discharged by the proved native source theorem. -/
theorem bangRecognition (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    Nonempty (BangRecognition c) := by
  rcases Nonsolvable.classified_bang_comparison c d sourceF h k small with hrow | hr
  · exact (not_rowTwo d c h k small hrow).elim
  · exact hr


open Chapter14.Section04.LargerDimension.LocalAction.Components
variable
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
    (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness thompson faithful b5 amalgams sourceF

/-- The literal plus quotient and both original parabolics, with F.6.16
constructed internally and no F.6.13 rigidity premise. -/
theorem core_and_marking (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      pPrimeCore 3 (I c) = pCore 2 (I c) ∧ Nonempty (ParabolicMarking c) := by
  obtain ⟨core,hcore,small⟩ := SourceCompletion.core_and_small d c structural uniqueness
    thompson faithful b5 amalgams geometry mark hcomm
  obtain ⟨recognition⟩ := bangRecognition d c sourceF geometry core small
  obtain ⟨hprime,marked⟩ := core_and_marking_of_bangRecognition c core recognition
  exact ⟨core,hcore,hprime,marked⟩

/-- The original point-generated module has rank three. Only the genuine
universal setup, B.5 and F.6 classification inputs remain; the native
noncyclic action and both core comparisons are constructed. -/
theorem primeRank_VI (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : primeRank 2 (VI c) = 3 := by
  obtain ⟨core,_,_,⟨parabolics⟩⟩ := core_and_marking d c structural uniqueness thompson
    faithful b5 amalgams sourceF geometry mark hcomm
  exact PointModule.primeRank_VI d c core parabolics geometry

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.Noncyclic
