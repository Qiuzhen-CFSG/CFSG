module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Generation
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Full innerness for the actual Janko four matrix model

The proved internal-fusion generation theorem discharges the sole remaining
premise of max1-centralizer amalgam rigidity. Thus every abstract automorphism
is conjugation by an element of the original model, and its outer group is
trivial. The two-group corollary is retained for the Chapter 1 inspection.

Source: GLS3 Table 5.3i, printed p.270 (Out(J₄) = 1); Aschbacher--Smith,
Theorem C, printed p.33, the inspection on p.510, and 16.1.5(9), p.1172.
No model simplicity or perfectness assumption is needed by this proof.
-/
public section
namespace Janko4.AdequateLocal

/-- Full innerness, without taking powers of the automorphism. -/
theorem conj_surjective : Function.Surjective (MulAut.conj : Model →* MulAut Model) :=
  Max1AmalgamRigidity.conj_surjective centralizer_sup_max1_eq_top

theorem exists_eq_conj (alpha : MulAut Model) : ∃ g : Model, alpha = MulAut.conj g := by
  obtain ⟨g, hg⟩ := conj_surjective alpha
  exact ⟨g, hg.symm⟩

/-- The actual quotient by the inner automorphisms is trivial. -/
theorem outer_subsingleton : Subsingleton (MulAut.Outer Model) := by
  have hone (x : MulAut.Outer Model) : x = 1 := by
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup Model) x
    exact (QuotientGroup.eq_one_iff f).mpr (conj_surjective f)
  exact ⟨fun x y => (hone x).trans (hone y).symm⟩

/-- The preserved weaker endpoint used by Chapter 1. -/
theorem outer_isPGroup_two : IsPGroup 2 (MulAut.Outer Model) := by
  let := outer_subsingleton
  exact IsPGroup.of_subsingleton 2 _

end Janko4.AdequateLocal
