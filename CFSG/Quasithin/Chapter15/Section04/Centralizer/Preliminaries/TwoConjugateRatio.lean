module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SourceInputs
public import CFSG.Quasithin.Chapter3.Defs

/-!
# The two-conjugate branch of 15.4.2(4)

For the original D=M₀/C_M₀(V) action on V, the earlier E.2.9/E.2.11 witness
inside H supplies A≤O₂(I)≤T≤M₀. Its image under the original quotient map
has kernel exactly Z and is a nontrivial elementary cubic actor with fixed
codimension at most twice its rank. Thus the original action has cubic ratio
at most two. No inclusion of Aut_H(V) into D is postulated.

The source setup retains 15.4.1 with the full known-simple catalogue and all
local assumptions of 15.4.2(4). `Witness` retains only the actual earlier
subgroup geometry, generalized-Fitting equality, and order-two quotient
image. Its construction belongs to qt-e02-witnesses and
qt-15-04-prime-reduction; the latter also owns the other qrc alternatives
and final assembly of the full source lemma.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed p.1156, case (i) in the proof of 15.4.2(4),
using E.2.9–13 on pp.221–225 and B.6.8(5).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.TwoConjugateRatio
open ChapterE TwoConjugate DihedralCubic
variable {G : Type*} [Group G] [Finite G]

/-- The literal local assumptions in 15.4.2(4). The R₂ condition is expanded
as relative normality, elementary abelianness, and a two-reduced faithful quotient. -/
structure LocalHypotheses (T : Sylow 2 G) (M₀ M V : Subgroup G) : Prop where
  mem_H : M₀ ∈ Chapter1.HOver G (T : Set G)
  unique_overgroup : maximalTwoLocalOvergroups M₀ = {M}
  le_M₀ : V ≤ M₀
  elementary : IsElementaryAbelian 2 V
  normalizes : M₀ ≤ normalizer (V : Set G)
  reduced : pCore 2 (ActionQuotient M₀ V normalizes) = ⊥
  centralizer_core : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    (M₀ ⊓ centralizer (V : Set G)).pCoreIn 2
  le_core : V ≤ M.pCoreIn 2

/-- Earlier-source witness data in the solvable branch: the actual I≤H,
its Sylow two-subgroup, the two conjugates, and the order-two quotient image.
These are outputs of E.2.9/E.2.11 and B.6.8(5), not ratio assumptions.
Their producers remain qt-e02-witnesses and qt-15-04-prime-reduction. -/
structure Witness (T : Sylow 2 G) (M V H I : Subgroup G) where
  mem_HStar : H ∈ Chapter3.HStar (T : Subgroup G) M
  le_H : I ≤ H
  le_I : V ≤ I
  sylow : Sylow 2 I
  sylow_le : (sylow : Subgroup I).map I.subtype ≤ (T : Subgroup G)
  conjugator : I
  geometry : Hypotheses sylow (V.subgroupOf I) ((M ⊓ H).subgroupOf I) conjugator
  proper : V.subgroupOf I ≠ ⊤
  fitting : generalizedFitting I = pCore 2 I
  quotient_card : Nat.card ((V.subgroupOf I).map
    (QuotientGroup.mk' (J ((M ⊓ H).subgroupOf I)))) = 2

variable {T : Sylow 2 G} {M₀ M V H I : Subgroup G}

/-- 15.4.2(4), case (i), with the two-conjugate witness supplied by the earlier
source. The representation is on the original V for D=M₀/C_M₀(V), and the
actor is the literal image of A≤O₂(I)≤T≤M₀. Full 15.4.1 retains the full
KnownSimple catalogue through SourceHypotheses. -/
theorem source_cubic_actor
    (_fullKnownSimple : MaximalPrimeSource.SourceHypotheses T)
    (l : LocalHypotheses T M₀ M V) (w : Witness T M V H I) :
    letI := l.elementary
    let ρ := canonicalAction M₀ V l.normalizes
    let f := actorMap w.geometry (w.sylow_le.trans l.mem_H.2)
      (projection M₀ V l.normalizes)
    f.ker = (Z (V.subgroupOf I) w.conjugator).subgroupOf
      (A (V.subgroupOf I) ((M ⊓ H).subgroupOf I) w.conjugator) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  let := l.elementary
  let := centralizer_normal M₀ V l.normalizes
  exact ambient_cubic_actor w.le_I l.normalizes w.geometry
    (w.sylow_le.trans l.mem_H.2) w.proper w.fitting w.quotient_card
    (projection M₀ V l.normalizes) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)

/-- The required upper bound for the original faithful D-action. Construction
of the earlier witness and the other qrc alternatives belongs to the parent. -/
theorem source_cubicRatio_le_two
    (fullKnownSimple : MaximalPrimeSource.SourceHypotheses T)
    (l : LocalHypotheses T M₀ M V) (w : Witness T M V H I) :
    letI := l.elementary
    cubicRatio (canonicalAction M₀ V l.normalizes) ≤ 2 :=
  (source_cubic_actor fullKnownSimple l w).2.2.2.2

end CFSG.Quasithin.Chapter15.Section04.TwoConjugateRatio
