module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.SourceRelations
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.EndpointSeparation
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.Checked
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case1.Checked
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Checked
/-!
# Wrong pointed reflection pairs cannot satisfy the octagonal braid

Each of the three nonstandard pointed-pair representatives is excluded in an
arbitrary faithful completion of the original full binary Ree amalgam. The
kernel-checked coset-word certificates use only the actual endpoint relations.
A wrong eighth-power braid would put the second reflection in the first image,
contrary to the verified endpoint orders. In particular, no product order from
an already recognized ambient Ree group is transported into the completion.

Source: Aschbacher–Smith F.4.8 and F.4.10, with the marked parabolics of F.4.4.
-/
public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.BadBraid
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G]

/-- The second reflection cannot be shifted by the common root-one element. -/
theorem bad_braid_shifted (c : Completion (G := G)) :
    (generator c 3 * (generator c 0)⁻¹ * generator c 4 * generator c 0)^8 ≠ 1 := by
  intro h
  apply reflection_not_mem_left c
  apply Case0.reflection_mem (generator c) c.left.range
    (first_generators_mem c) (source_relations c)
  simpa only [Case0.badWord, eval_cons, eval_nil, Bool.true_eq, Bool.false_eq_true,
    ↓reduceIte, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h

/-- Twisting the first reflection by root nine is incompatible with the braid. -/
theorem bad_braid_twisted (c : Completion (G := G)) :
    (generator c 2 ^ 2 * generator c 3 * generator c 4)^8 ≠ 1 := by
  intro h
  apply reflection_not_mem_left c
  apply Case1.reflection_mem (generator c) c.left.range
    (first_generators_mem c) (source_relations c)
  simpa only [Case1.badWord, eval_cons, eval_nil, Bool.true_eq, Bool.false_eq_true,
    ↓reduceIte, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h

/-- Simultaneously twisting the first and shifting the second also fails. -/
theorem bad_braid_twisted_shifted (c : Completion (G := G)) :
    (generator c 2 ^ 2 * generator c 3 * (generator c 0)⁻¹ *
      generator c 4 * generator c 0)^8 ≠ 1 := by
  intro h
  apply reflection_not_mem_left c
  apply Case2.reflection_mem (generator c) c.left.range
    (first_generators_mem c) (source_relations c)
  simpa only [Case2.badWord, eval_cons, eval_nil, Bool.true_eq, Bool.false_eq_true,
    ↓reduceIte, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using h

end Tits.AmalgamRigidity.FullRee.BadBraid
