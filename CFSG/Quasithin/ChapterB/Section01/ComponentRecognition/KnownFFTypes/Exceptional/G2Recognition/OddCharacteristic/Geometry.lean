module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.G2Recognition.OddCharacteristic.Geometry.Normalizer
public import Theory.GroupTheory.AutomorphismRankCyclicOuter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

/-!
# Assembling odd-field G₂ geometry from intrinsic model results

The elementary-subgroup size bound gives inner two-rank at most three.
Centerlessness identifies the actual model with its inner automorphism group,
and a cyclic outer quotient adds at most one. Independently, generation by
eight conjugates under model elements lifts through every perfect central
cover and the scalar centralizer to the literal full binary normalizer.

These reductions discharge the transport and rank arithmetic, not the three
model contracts in `Geometry.ModelInputs`. Final geometry assembly must prove
all three contracts. The source-theorem exclusion remains with
`OddCharacteristic.not_ff_of_model_bounds`.

Sources: Guralnick–Malle, Classification of 2F-modules I, §2 and Proposition 4.6;
GLS III, Theorem 2.5.12, for the odd G₂ outer quotient, including characteristic
three. The eight-conjugate bound is a proposed sufficient bound to be proved.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd
universe u v w

/-- Elementary size eight and a cyclic full outer quotient give automorphism
rank four. Centerlessness is supplied by the existing actual-model theorem. -/
theorem automorphism_rank_le_four_of_model_inputs
    {F : Type v} [Field F] [Finite F] (hq : 2 < Nat.card F)
    (hsize : ∀ E : Subgroup (Atlas.G2.Model F),
      IsElementaryAbelian 2 E → Nat.card E ≤ 8)
    [IsCyclic (MulAut.Outer (Atlas.G2.Model F))] :
    primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 4 := by
  have hr : primeRank 2 (Atlas.G2.Model F) ≤ 3 :=
    (primeRank_le_iff_elementary_card_le (Atlas.G2.Model F)).mpr hsize
  exact (automorphism_twoRank_le_of_cyclic_outer
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq)).trans
      (Nat.add_le_add_right hr 1)

/-- The two independent intrinsic rank inputs produce the unchanged rank predicate. -/
theorem automorphismRankBound_of_model_inputs
    (hsize : Geometry.ModelElementaryTwoBound.{v})
    (houter : Geometry.ModelOuterCyclic.{v}) : AutomorphismRankBound.{v} := by
  intro F _ _ hq hchar
  let := houter F hq hchar
  exact automorphism_rank_le_four_of_model_inputs hq (hsize F hq hchar)

/-- Intrinsic inner-conjugate generation supplies the published normalizer
predicate, for every central cover and every faithful irreducible binary action. -/
theorem largeFieldConjugateBound_of_model_input
    (hgen : Geometry.ModelEightConjugateBound.{v}) :
    LargeFieldConjugateBound.{u,v,w} := by
  intro R _ _ _ F _ _ hq hchar e _ W _ _ _ σ hf hi t ht ht2
  exact Geometry.normalizer_conjugate_generation σ hf hi e 8 (hgen F hq hchar) t ht ht2

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.G2Odd
