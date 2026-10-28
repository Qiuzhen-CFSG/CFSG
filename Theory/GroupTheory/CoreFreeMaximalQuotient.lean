module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Order.Atoms

/-!
# Quotients and core-free maximal subgroups

If `P` is a core-free maximal subgroup of `G`, every noninjective
surjection from `G` is still surjective on `P`. Indeed, its nontrivial
normal kernel cannot lie in `P`, so the kernel together with `P` generates
`G`. This elementary observation lets a subgroup induction treat quotients
of whole groups without first proving those groups simple.
-/

namespace Subgroup

/-- A noninjective quotient is already an image of a core-free maximal subgroup. -/
public theorem surjective_domRestrict_of_coatom_normalCore_eq_bot
    {G S : Type*} [Group G] [Group S] (P : Subgroup G)
    (hP : IsCoatom P) (hcore : P.normalCore = ⊥)
    (f : G →* S) (hf : Function.Surjective f) (hni : ¬ Function.Injective f) :
    Function.Surjective (f.domRestrict P) := by
  have hker : ¬ f.ker ≤ P := by
    intro h
    have hh : f.ker ≤ P.normalCore := Subgroup.normal_le_normalCore.mpr h
    rw [hcore] at hh
    exact hni (f.ker_eq_bot_iff.mp (le_bot_iff.mp hh))
  have hsup : P ⊔ f.ker = ⊤ := hP.lt_iff.mp (lt_of_le_of_ne le_sup_left (by
    intro h
    apply hker
    simpa only [← h] using (le_sup_right : f.ker ≤ P ⊔ f.ker)))
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.domRestrict_range]
  have hm := congrArg (Subgroup.map f) hsup
  simpa only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
    Subgroup.map_top_of_surjective f hf] using hm

end Subgroup
