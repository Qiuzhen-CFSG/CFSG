module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Nonsolvable
public import CFSG.Quasithin.Chapter3.Section01.E23Input

/-!
# The nonsolvable qrc action in its original coordinates

The original qrc hypotheses construct U as the Sylow omega-center orbit
in H. Applying the genuine E.2.3 reduction identifies E(A)=F*(A)=O²(A)
for A=H/C_H(U) and proves that this residual centralizes F(A).
Nonsolvability is assumed only for the original H branch and is proved
for A by the source reduction. No semisimplicity or model premise is used.

Source: Aschbacher–Smith, 3.1.7 and the B.6.9 reduction underlying E.2.3,
printed pp.575–576,116,216–217 (1 March 2004 manuscript). The individual
natural factors and the Baumann Sylow conclusion remain separate steps.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.e23_nonsolvable_residual
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hs : ¬ Group.IsSolvable H) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI := hU.normal
    let A := H ⧸ centralizer (U : Set H)
    componentLayer A = pResidual 2 A ∧ generalizedFitting A = pResidual 2 A ∧
      pResidual 2 A ≤ centralizer (fittingSubgroup A : Set A) := by
  obtain ⟨_, _, hp, hU, hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  exact ChapterE.ThompsonAction.source_nonsolvable_residual _ hp _ hU hs hj

end CFSG.Quasithin.Chapter3
