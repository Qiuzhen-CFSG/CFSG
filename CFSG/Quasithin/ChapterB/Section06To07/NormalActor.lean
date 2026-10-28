module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.GroupTheory.Commutator.ResidualNormalGeneration
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# A Sylow-normalized two-actor generates the minimal-parabolic residual

For R≤S normalized by S and outside O₂(H), its normal closure lies outside
the core of the unique maximal overgroup: S intersects that core in O₂(H).
B.6.8(4) makes the closure contain O²(H), and residual normal generation
then gives O²(H)=[O²(H),R]. All groups and embeddings remain literal.
Source: Aschbacher–Smith, B.6.8(4–5), D.1.4, pp.113–115,176.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H] [Finite H]
theorem minimalParabolic_residual_commutator_of_normalized_two_actor
    (S : Sylow 2 H) (hP : IsMinimalParabolicOver S ⊤) (R : Subgroup H)
    (hRS : R ≤ S) (hSR : (S : Subgroup H) ≤ normalizer (R : Set H))
    (hRcore : ¬ R ≤ pCore 2 H) : pResidual 2 H = ⁅pResidual 2 H,R⁆ := by
  have hnot : ¬ normalClosure (R : Set H) ≤ minimalParabolicCore S hP := by
    intro h
    apply hRcore
    rw [← minimalParabolic_sylow_inf_core S hP]
    exact le_inf hRS ((show R ≤ normalClosure (R : Set H) from fun _ hx => le_normalClosure hx).trans h)
  have hKN := (minimalParabolic_normal_subgroup_residual_dichotomy S hP
    (normalClosure (R : Set H))).resolve_left hnot
  exact eq_commutator_of_normalClosure_contains (pResidual 2 H) S R
    (pResidual_sup_sylow_eq_top S) (isPPerfect_pResidual 2)
    (S.isPGroup'.to_le hRS) hSR hKN
end CFSG.Quasithin.ChapterB

