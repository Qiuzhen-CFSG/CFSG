module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Nonsolvable
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# The nonsolvable reduced-image reduction for E.2.3

The actual centralizer quotient is minimal parabolic and has trivial
two-core. Its kernel lies in the solvable maximal-overgroup core, so
nonsolvability of H survives in the quotient. B.2.7 supplies the faithful
FF action, and the proved B.1.9 reduction identifies its two-residual
with both its layer and generalized Fitting subgroup. Every quotient map
is the original map on U; no component classification is assumed.

Source: Aschbacher–Smith, B.6.9 and E.2.3, printed pp.116 and216–217
(1 March 2004). Recognition of the individual natural factors remains
the next independent classification step.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The nonsolvable reduced image has its actual residual equal to its component layer. -/
theorem nonsolvable_residual
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hcore : pCore 2 H = ⊥) (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    componentLayer H = pResidual 2 H ∧ generalizedFitting H = pResidual 2 H ∧
      pResidual 2 H ≤ centralizer (fittingSubgroup H : Set H) := by
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker, he]
    exact le_top
  obtain ⟨hk, hp⟩ := ChapterB.minimalParabolic_reduced_image T hP q hq hcore hn
  have hsH : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    let := ChapterB.minimalParabolic_core_solvable T hP
    let : Group.IsSolvable q.ker :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hk) (inclusion_injective hk)
    exact hs (Group.isSolvable_of_ker_le_range q.ker.subtype q (by rw [range_subtype]))
  obtain hf | ⟨_, hff, _, _, _⟩ := ChapterB.lemma_B_2_7 U q hq hker T
  · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hfaith := NormalElementaryQuotient.representation_injective U q hq hker
  have he := ChapterB.minimalParabolic_nonsolvable_semisimple_residual ρ
    (T.mapSurjective hq) hp hsH hcore hfaith hff
  exact ⟨he.1, he.2, ChapterB.minimalParabolic_nonsolvable_residual_centralizes_fitting ρ
    (T.mapSurjective hq) hp hsH hcore hfaith hff⟩

variable {G : Type*} [Group G] [Finite G]
/-- The original reduced subgroup, with its literal centralizer quotient. -/
theorem source_nonsolvable_residual
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    let H := G ⧸ centralizer (U : Set G)
    componentLayer H = pResidual 2 H ∧ generalizedFitting H = pResidual 2 H ∧
      pResidual 2 H ≤ centralizer (fittingSubgroup H : Set H) := by
  let := hU.normal
  let := hU.elementary
  exact nonsolvable_residual T hP U _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hs hJ

end CFSG.Quasithin.ChapterE.ThompsonAction
