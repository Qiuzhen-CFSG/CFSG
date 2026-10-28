module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SmallRatio
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SourceInputs
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.Representation.NormalElementaryQuotient

/-!
# The solvable dual-FF branch of 15.4.2(4)

The earlier 15.4.2(2) implication makes the actual maximal two-local M
solvable, hence also M₀ and its centralizer quotient. Reducedness gives
trivial two-core of that same quotient. The canonical quotient action is
faithful, so the solvable dual-FF bound applies to the original V and its
actual dual. This discharges precisely the dual-FF case of the qrc argument.

The original local-overgroup, centralizer-kernel and two-core containment
hypotheses are retained at the source boundary. Only a subset is needed
in this branch. The universal earlier 15.4.2(1–3) theorem remains the
obligation of qt-15-04-prime-reduction. The other qrc cases and the full
15.4.2(4) implication are not asserted here.

Source: Aschbacher–Smith, 15.4.2(4), printed p.1156. B.1.8 on the solvable
acting quotient supplies the bound directly in place of general B.5.13.
-/

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.SolvableDualFF
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal dual-FF branch of 15.4.2(4), on M₀/C_M₀(V).
Solvability and faithfulness are derived, not added as source premises. -/
public theorem source_lemma_15_4_2_four_of_dualFF
    (T : Sylow 2 G) (h : SourceHypotheses T) (h42 : Earlier1542 (G := G))
    (M₀ M : Subgroup G) (hM₀ : M₀ ∈ Chapter1.HOver G (T : Set G))
    (hM : IsMaximalTwoLocal M) (hM₀M : M₀ ≤ M)
    (_hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (V : Subgroup M₀) (hV : IsPReduced 2 V) :
    letI := hV.normal
    letI := hV.elementary
    (T : Subgroup G).subgroupOf M₀ ⊓ centralizer (V : Set M₀) =
      (centralizer (V : Set M₀)).pCoreIn 2 →
    V.map M₀.subtype ≤ M.pCoreIn 2 →
    IsFFModule (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).dual →
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let := hV.normal
  let := hV.elementary
  intro _hkernel _hVcore hff
  have hTM : (T : Subgroup G) ≤ M := fun x hx => hM₀M (hM₀.2 hx)
  let : Group.IsSolvable M := (h42 T h).solvable M hM hTM
  let : Group.IsSolvable M₀ :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hM₀M)
      (inclusion_injective hM₀M)
  let C := centralizer (V : Set M₀)
  let q := QuotientGroup.mk' C
  let ρ := Representation.NormalElementaryQuotient.representation V q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  change cubicRatio ρ ≤ 2
  change IsFFModule ρ.dual at hff
  exact ChapterB.SolvableDualFF.cubicRatio_le_two ρ inferInstance
    hV.quotient_pCore_eq_bot
    (Representation.NormalElementaryQuotient.representation_injective V q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) hff

end CFSG.Quasithin.Chapter15.Section04.SolvableDualFF
