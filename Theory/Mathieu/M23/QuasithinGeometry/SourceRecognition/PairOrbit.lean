module
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.AlternatingSection
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# All pairs in the original native heptad orbit

The alternating section realizes any ordered pair of distinct heptad labels.
Consequently the actual heptad-stabilizer orbit of the standard pair is exactly
the set of two-subsets of its heptad. This supplies the geometric target for
the source coset-orbit comparison, with the original labelled action.

Source: Aschbacher–Smith 5.2.19(2), printed p.656 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

/-- The native heptad orbit is exactly all unordered pairs of its seven points. -/
theorem heptad_pair_orbit : MulAction.orbit heptadStabilizer x.val =
    {p : Finset (Fin 23) | p.card = 2 ∧ p ⊆ omega} := by
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    refine ⟨?_,?_⟩
    · simpa only [Finset.card_smul_finset] using x.property
    · have hh := Finset.smul_finset_subset_smul_finset (a := (g : M23))
        (x_subset_lambda.trans lambda_subset_omega)
      rwa [show (g : M23) • omega = omega from g.property] at hh
  · rintro ⟨hp,hpω⟩
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hp
    have ha : a ∈ omega := hpω (by simp)
    have hb : b ∈ omega := hpω (by simp)
    obtain ⟨i,hi⟩ := labelEquiv.surjective ⟨a,ha⟩
    obtain ⟨j,hj⟩ := labelEquiv.surjective ⟨b,hb⟩
    have hi' : label i = a := congrArg Subtype.val hi
    have hj' : label j = b := congrArg Subtype.val hj
    have hij : i ≠ j := by intro he; exact hab (hi'.symm.trans (he ▸ hj'))
    have := alternatingGroup.isMultiplyPretransitive (Fin 7)
    have ht : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 7)) (Fin 7) 2 :=
      MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 7) - 2) (by simp) (Nat.sub_le _ _)
    obtain ⟨g,hg5,hg6⟩ := MulAction.is_two_pretransitive_iff.mp ht
      (by decide : (5 : Fin 7) ≠ 6) hij
    refine ⟨AlternatingSection.s g,?_⟩
    change (AlternatingSection.s g : M23) • ({label 5,label 6} : Finset (Fin 23)) = {a,b}
    simp only [Finset.smul_finset_insert,Finset.smul_finset_singleton,
      ←heptadAction_apply,AlternatingSection.heptadAction_s]
    rw [show g.val 5 = i from hg5,show g.val 6 = j from hg6,hi',hj']

end Sporadic.Mathieu.M23Geometry
