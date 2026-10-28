module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCoreHyperplanes
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenContradiction

/-!
# Assembly of the chosen-module terminal arguments

Hyperplane centralizer control gives `r > 1`. The earlier action parameters
then give `s > 1` and actual zeroth weak closure, while the independent
partner-core containment and 15.2.15 give the plane-overlap implication by
Burnside fusion. These deductions supply the corresponding inputs of the
already proved normal-closure and E.3.6 contradiction.

This is a conditional assembly. It does not assert 15.2.25, the hyperplane
geometry of 15.2.26, partner-core containment in 15.2.27(2), or existence of
the two-sided corank-one critical pair. Those source branches must be
proved and their premises discharged before Section 15.2 is complete. The
second assembly discharges the hyperplane argument from partner-core containment.

Source: Aschbacher--Smith, 15.2.25--28 and the terminal argument,
printed pp.1118--1120.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open ChapterD ChapterD.UniqueFactor ChapterE

variable {G : Type*} [Group G] [Finite G]

/-- Assembly with the remaining source arguments explicit. In particular
the overlap implication and the global weak-closure parameter are derived. -/
theorem source_chosen_contradiction_of_hyperplanes_core_and_pair
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1)
    (hhyper : ∀ U ≤ V, subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hcore : V ≤ twoCoreIn Mc)
    (hTS : ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
      x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G))
    (hcomm : ⁅V, (T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS)
    (hpair : ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  let := h.prepared.elementary
  have hr := one_lt_globalR_of_hyperplane_centralizers V hhyper
  obtain ⟨hs, hW, _⟩ := source_chosen_weakClosure_of_globalR T h H hgeo.outside hr hm ha
  have hoverlap := source_chosen_overlap_of_core T h hgeo hu (hW.trans inf_le_right) hcore
  obtain ⟨g, hfirst, hsecond, hmove⟩ := hpair
  exact source_chosen_contradiction_of_critical_pair T h H ZS hgeo hTS hcomm hs
    hoverlap g hfirst hsecond hmove

/-- Final assembly after the independent involution, partner-core and
critical-pair branches. Hyperplane control is derived from the partner core. -/
theorem source_chosen_contradiction_of_core_and_pair
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1)
    (hcore : V ≤ twoCoreIn Mc)
    (hTS : ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
      x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G))
    (hcomm : ⁅V, (T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS)
    (hpair : ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  exact source_chosen_contradiction_of_hyperplanes_core_and_pair T h hgeo hu hm ha
    (fun U _ hU => source_chosen_hyperplane_centralizer_of_core h hgeo hu hcore U hU)
    hcore hTS hcomm hpair

end CFSG.Quasithin.Chapter15.Section02
