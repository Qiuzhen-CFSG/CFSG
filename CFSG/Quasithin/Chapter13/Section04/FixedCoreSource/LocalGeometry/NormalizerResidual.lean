module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Normalizer
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.ThetaSixSource
public import Theory.GroupTheory.CComponent.AlternatingResidual

/-!
# The actual normalizer residuals in source 13.4.2(5)

The source uniqueness theorem places L as a relatively normal C-component
of its full ambient normalizer. The local SQTK three-rank bound and the
ordinary A₆ outer action identify its literal prime-to-three residual with
L. For either central-cover row, the six-letter action quotient gives the
cubic generation identity in the same normalizer.

These statements retain the two-core quotient in the ordinary residual
clause and the central-core quotient in the cubic-generation clause.
Source: Aschbacher--Smith 12.2.8 and 13.4.2(5), printed pp.797 and 897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ordinary clause of 13.4.2(5), with the full ambient embedding. -/
theorem normalizer_primeToThree_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L := by
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  have hc := h.source_normalizer_component structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hs := h.source_normalizer_sqtk structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  exact hc.map_primeToResidual_three_eq_of_quotient_alternating L.le_normalizer le_rfl
    (Or.inl rfl) e (hs.stronglyQuasithin 3 Nat.prime_three (by decide))

/-- Cubics generate L in either original five-dimensional central-cover row. -/
theorem normalizer_theta
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    closure {x : G | x ∈ normalizer (L : Set G) ∧ orderOf x = 3} = L := by
  exact h.toHypothesis1221.source_theta_eq_of_six_action_quotient
    D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) m.quotient

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
