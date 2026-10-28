module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.InsideCore.Transport
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.CommonNormal

/-!
# The inside-core branch of 15.4.2(4)

For H ∈ H*(T,M) with V ≤ O₂(H), apply genuine universal D.1.5 to the
QRC configuration supplied by the original local hypotheses. Its quadratic
bounds transport to M₀/C_M₀(V) acting on intrinsic V and imply the cubic
bound. The dual-FF case uses the already proved solvable dual-FF theorem.

In the unique-noncentral-chief-factor case, A/C makes H solvable, and even
characteristic identifies F*(H) with O₂(H). The genuine universal Sylow
implication of D.1.4 then either gives the same dual-FF case or gives
O₂(M₀) ∈ Syl₂(O²(H)O₂(M₀)), contrary to the proved application of 3.1.1.
Thus no local premise remains beyond the task's source hypotheses.

The universal D.1 inputs remain with qt-d-01 and qt-d-01-unique-factor;
3.1.1 remains with qt-3-01/qt-c-05. Universal A/C and the outside-core branch
remain with the parent qt-15-04-ratio-source, which owns Earlier1542Four
assembly. This module proves the complete conditional inside-core contract.

Source: Aschbacher–Smith, 15.4.2(4), printed p.1156, and D.1.4–5,
printed pp.175–177, refs/quasithin.pdf (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open InsideCore MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₀ M : Subgroup G} {V : Subgroup M₀}

/-- The entire inside-core branch of source 15.4.2(4), on the original
centralizer quotient and intrinsic V. Only genuine earlier universal source
implications remain explicit; every local hypothesis of D.1 is discharged. -/
theorem LocalHypotheses.cubicRatio_le_two_of_inside_core
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (hD15 : EarlierD15.{u}) (hD14 : EarlierD14Sylow.{u})
    (l : LocalHypotheses T M₀ M V) (h : SourceHypotheses T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hin : V.map M₀.subtype ≤ H.pCoreIn 2) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let := l.reduced.normal
  let := l.reduced.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
  let d := l.qrc hH
  have hn := l.module_ne_bot h h311
  have hdual : IsFFModule (imageRepresentation M₀ (V.map M₀.subtype) l.normalizes).dual →
      cubicRatio (Representation.NormalElementaryQuotient.representation V
        (QuotientGroup.mk' (centralizer (V : Set M₀)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
    intro hf
    exact cubicRatio_le_two_of_dualFF hA hC T h M₀ l.mem_H V l.reduced
      (l.dualFF_of_image hf)
  rcases hD15 G M₀ H (T : Subgroup G) (V.map M₀.subtype) d hn with
    hout | hq | hf | hmultiple | hunique
  · exact (hout hin).elim
  · exact (cubicRatio_le_quadraticRatio _).trans
      (l.quadraticRatio_le_two_of_image (hq.1.trans (by norm_num)))
  · exact hdual hf
  · exact (cubicRatio_le_quadraticRatio _).trans
      (l.quadraticRatio_le_two_of_image hmultiple.1)
  · rcases hD14 G M₀ H (T : Subgroup G) (V.map M₀.subtype) d hn hin
      hunique.2.2.1 (solvable_of_mem_HOver hA hC T h hH.1.1)
      (fitting_eq_core_of_HStar h hH) with hf | hs
    · exact hdual hf
    · exact (l.not_core_sylow h h311 hH hs).elim

end CFSG.Quasithin.Chapter15.Section04.RatioSource
