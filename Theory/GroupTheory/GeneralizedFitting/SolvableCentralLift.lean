module

public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.GroupTheory.IsPerfect


/-!
# Generalized Fitting bounds across a solvable central extension

If a finite group's solvable image has trivial odd prime cores and the
kernel is central, the original group is solvable. Every odd prime core
maps trivially and hence lies in the kernel. The prime-core formula for
Fitting and the absence of components therefore give
F*(G) ≤ O₂(G) ker(f), retaining any odd central factor.

This is the central-extension step used for the genuine triple cover of
A₆ in Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.13,
printed p.74 (PDF p.85). The application restricts the coordinate map to
each actual overgroup; no containment of the full central kernel is needed.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- A solvable image with no odd prime cores bounds F* upstairs, retaining the central kernel. -/
theorem generalizedFitting_le_twoCore_sup_central_kernel
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    [Group.IsSolvable H]
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → pCore p H = ⊥) :
    generalizedFitting G ≤ pCore 2 G ⊔ f.ker := by
  let : Group.IsSolvable (center G) := Group.isSolvable_of_comm fun x y =>
    Subtype.ext ((mem_center_iff.mp x.property y).symm)
  let : Group.IsSolvable f.ker :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
  let : Group.IsSolvable G := Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)
  apply sup_le
  · rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.val.val = 2
    · rw [hp]
      exact le_sup_left
    · have hmap : (pCore p.val.val G).map f ≤ pCore p.val.val H :=
        le_sSup ⟨(inferInstance : (pCore p.val.val G).Normal).map f hf, pCore_isPGroup.map f⟩
      rw [hodd p.val.val (Fact.out : p.val.val.Prime) hp] at hmap
      exact ((Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hmap)).trans le_sup_right
  · apply sSup_le
    intro M hM
    let : IsQuasisimple M := hM.2
    let : IsSimpleGroup (M ⧸ center M) := IsQuasisimple.simple
    let : Nontrivial M := (QuotientGroup.mk'_surjective (center M)).nontrivial
    exact (Group.IsPerfect.not_isSolvable M inferInstance).elim
end Theory.GroupTheory
