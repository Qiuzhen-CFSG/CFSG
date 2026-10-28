module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Complete

/-!
# The completed Gol80 size bounds

The canonical labels, radius restriction, and the compatible G₂ and Mathieu
recognitions discharge the four source cuts in the numerical Goldschmidt
theorem. Thus a finite Goldschmidt triple with trivial ambient two-core has
overlap of order at most 128 and each vertex of order at most 384.

The vertex bound is the literal amalgam premise used by Chapter 14's original
critical-path argument.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Theorem A,
Table 1 and Sections 3--6, pp.378--406.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
open SourceAssembly.Goldschmidt

variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- The common Sylow subgroup of a finite Goldschmidt triple has order at most
128 when the ambient two-core is trivial. All Gol80 source cuts are proved. -/
theorem IsGoldschmidtTriple.intersection_card_le_128
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    Nat.card (A ⊓ B : Subgroup G) ≤ 128 :=
  h.intersection_card_le_128_of_source_cuts canonicalLabelsInput canonicalRadius
    radiusTwoMarkedInput MathieuRadiusThree.radiusThreeMarkedInput hcore

/-- The universal Gol80 vertex-size bound used by Chapter 14. -/
theorem IsGoldschmidtTriple.card_le_384
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) : Nat.card A ≤ 384 :=
  h.card_le_384_of_source_cuts canonicalLabelsInput canonicalRadius
    radiusTwoMarkedInput MathieuRadiusThree.radiusThreeMarkedInput hcore

end CFSG.Quasithin.ChapterF
