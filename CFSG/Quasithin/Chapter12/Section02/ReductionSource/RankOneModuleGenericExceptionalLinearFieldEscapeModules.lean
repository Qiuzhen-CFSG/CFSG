module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesRatio
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# The strict bound on the original escaping-cubic action

The actual residual quotient of H identifies the normal PSL₃(4) subgroup
of H/O₂(H). The faithful-section argument supplies the strict quadratic
bound for every literal action on the H-span modulo ⟨z⟩. In particular,
the final F.9.16 contradiction no longer needs a strict-ratio premise.

The local construction and the abelian centralizer-span statement 5.1.23
remain separate source obligations. They are retained explicitly in the
conditional field-four consumer below.

Source: Aschbacher--Smith, final paragraph of 5.1.14, printed p.646;
12.2.2, printed p.795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ}

/-- The lower bound for the same literal action used by
`CubicEscape.LocalData.exists_bounded_action`. The point and local data
need no extra properties for this representation-theoretic conclusion. -/
theorem linear_cubic_quadraticRatio_gt_two
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (z : G) (hU : IsElementaryAbelian 2 (conjugateSpanBy (CubicEscape.plane C z) H)) :
    letI := hU
    ∀ a : LocalQuotientAction H (conjugateSpanBy (CubicEscape.plane C z) H) (zpowers z),
      2 < quadraticRatio a.representation := by
  let := hU
  intro a
  exact CubicEscape.localQuotientAction_quadraticRatio_gt_two _ _ _
    (Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1) hlinear a

/-- Discharge the old strict-ratio premise on the action constructed by
F.9.16. Only local existence and 5.1.23 remain to be supplied. -/
theorem linear_cubic_false_of_local_and_abelian_sources
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hlocal : ∃ z : G, CubicEscape.LocalData T H C z)
    (habelian : ∀ z : G, CubicEscape.LocalData T H C z →
      IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
        (centralizer ({z} : Set G)))) : False := by
  apply linear_cubic_false_of_local_and_module_sources hlocal habelian
  intro z _ hU
  exact linear_cubic_quadraticRatio_gt_two h hH hlinear z hU

/-- The original Cartan consumer with the strict bound proved, rather
than supplied as an additional source assumption. -/
theorem field_four_and_borel_of_linear_local_abelian_sources
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : LinearFieldCartan T L H A B C n)
    (hinside : C ≤ normalizer (residual H : Set G) → A = B)
    (hlocal : ¬ C ≤ normalizer (residual H : Set G) →
      ∃ z : G, CubicEscape.LocalData T H C z)
    (habelian : ∀ z : G, CubicEscape.LocalData T H C z →
      IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
        (centralizer ({z} : Set G)))) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T := by
  apply D.field_four_and_borel_of_linear_cubic_branches h hH hK hnf c hinside
  intro hout
  exact linear_cubic_false_of_local_and_abelian_sources h hH hlinear (hlocal hout) habelian

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
