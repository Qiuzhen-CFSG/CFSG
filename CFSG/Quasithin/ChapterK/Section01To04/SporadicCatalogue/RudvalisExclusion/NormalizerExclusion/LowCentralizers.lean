module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Maximality
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.Quotient

/-!
# Maximal centralizers of the marked low-displacement Rudvalis involutions

The marked comparison and the certified max6 word identify the ambient
centralizer for every conjugate of the literal matrix generator b squared.
The model calculation gives a double centralizer of order at most two.
Consequently the ambient center also has order at most two; binary
irreducibility and faithfulness kill every possible central involution.
The supplied quasisimplicity then makes the model simple and its two-core
trivial. The earlier unconditional odd-index maximal two-core theorem,
together with the certified radical-normalizer cover, gives maximality.

This discharges exactly LowInvolutionCentralizers, with no extra model,
maximality or centralizer premise. The parent normalizer-exclusion assembly
uses it in sourceNormalizerExclusion_of_modelFacts.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Ru paragraph, manuscript p.17, https://agag-malle.math.rptu.de/~malle/download/failfact.dvi;
GLS3 Table 5.3r, refs/KGroup/GLS3/Chapter5(sec3-).tex.
-/

public section

open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion

private theorem exists_marked_low_equiv (hmodel : StandardComparison)
    (t : standardGroup) (ht : IsConj t (standardB^2)) :
    ∃ e : Rudvalis.Model ≃* standardGroup,
      e Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.centralInvolution = t := by
  obtain ⟨e, _, hb⟩ := hmodel
  have hb' : e Rudvalis.b = standardB := Subtype.ext hb
  obtain ⟨g, hg⟩ := isConj_iff.mp ht.symm
  refine ⟨((MulAut.conj Rudvalis.LowCentralizers.squareConjugator).trans e).trans
    (MulAut.conj g), ?_⟩
  simp only [MulEquiv.trans_apply]
  rw [Rudvalis.LowCentralizers.squareConjugator_alignment, map_pow, hb']
  exact hg

theorem low_doubleCentralizer_card_le_two (hmodel : StandardComparison)
    (t : standardGroup) (ht : IsConj t (standardB^2)) :
    Nat.card (centralizer (centralizer ({t} : Set standardGroup) : Set standardGroup)) ≤ 2 := by
  obtain ⟨e, he⟩ := exists_marked_low_equiv hmodel t ht
  rw [← he, card_doubleCentralizer_equiv, ← Rudvalis.LowCentralizers.max6_eq_centralizer]
  exact Rudvalis.LowCentralizers.max6_doubleCentralizer_card_le_two

theorem standard_center_eq_bot_of_comparison (hmodel : StandardComparison)
    (hi : standardRepresentation.IsIrreducible) : center standardGroup = ⊥ := by
  let C := centralizer ({standardB ^ 2} : Set standardGroup)
  have hle : center standardGroup ≤ centralizer (C : Set standardGroup) := by
    intro z hz
    exact mem_centralizer_iff.mpr fun g _ => mem_center_iff.mp hz g
  have hc : Nat.card (center standardGroup) ≤ 2 :=
    (Nat.card_le_card_of_injective _ (inclusion_injective hle)).trans
      (low_doubleCentralizer_card_le_two hmodel (standardB^2) (IsConj.refl _))
  have hcpos : 0 < Nat.card (center standardGroup) := Nat.card_pos
  have hdiv : Nat.card (center standardGroup) ∣ 2 := by
    have hcases : Nat.card (center standardGroup) = 1 ∨
        Nat.card (center standardGroup) = 2 := by omega
    rcases hcases with h | h <;> simp [h]
  let : Representation.IsIrreducible
      (standardRepresentation.comp (⊤ : Subgroup standardGroup).subtype) :=
    (Representation.irreducible_comp_surjective_iff (⊤ : Subgroup standardGroup).subtype
      (fun x => ⟨⟨x, mem_top x⟩, rfl⟩) standardRepresentation).mpr hi
  apply le_bot_iff.mp
  intro z hz
  rw [mem_bot]
  have hz2 : (⟨z, hz⟩ : center standardGroup)^2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans hdiv)
  apply BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    standardRepresentation (⊤ : Subgroup standardGroup) standardRepresentation_injective
    (congrArg Subtype.val hz2)
  exact mem_centralizer_iff.mpr fun g _ => mem_center_iff.mp hz g

private theorem model_isSimple (hmodel : StandardComparison)
    (hq : IsQuasisimple standardGroup) (hi : standardRepresentation.IsIrreducible) :
    IsSimpleGroup Rudvalis.Model := by
  let : IsSimpleGroup (standardGroup ⧸ center standardGroup) := hq.simple
  let : IsSimpleGroup standardGroup :=
    ((QuotientGroup.quotientMulEquivOfEq (standard_center_eq_bot_of_comparison hmodel hi)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨e, _, _⟩ := hmodel
  exact e.isSimpleGroup

private theorem model_twoCore_eq_bot [IsSimpleGroup Rudvalis.Model] :
    pCore 2 Rudvalis.Model = ⊥ := by
  rcases (inferInstance : (pCore 2 Rudvalis.Model).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hp : IsPGroup 2 Rudvalis.Model := by
      have hh := pCore_isPGroup (p := 2) (G := Rudvalis.Model)
      rw [h] at hh
      exact hh.of_equiv (Subgroup.topEquiv)
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hd : 13 ∣ 2^n := by
      rw [← hn, ← Rudvalis.orderOf_ab]
      exact orderOf_dvd_natCard _
    have hf : 13 ∣ 2 := (show Nat.Prime 13 by decide).dvd_of_dvd_pow hd
    norm_num at hf

theorem lowInvolutionCentralizers (hmodel : StandardComparison)
    (hq : IsQuasisimple standardGroup) (hi : standardRepresentation.IsIrreducible) :
    LowInvolutionCentralizers := by
  let : IsSimpleGroup Rudvalis.Model := model_isSimple hmodel hq hi
  have hmax : IsCoatom Rudvalis.SylowOvergroups.max6 :=
    Rudvalis.LowCentralizers.max6_isCoatom_of_twoCore model_twoCore_eq_bot
      Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
  intro t ht
  refine ⟨?_, low_doubleCentralizer_card_le_two hmodel t ht⟩
  obtain ⟨e, he⟩ := exists_marked_low_equiv hmodel t ht
  rw [← he, isCoatom_centralizer_equiv_iff, ← Rudvalis.LowCentralizers.max6_eq_centralizer]
  exact hmax
end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion
