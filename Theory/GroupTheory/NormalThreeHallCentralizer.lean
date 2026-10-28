module
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Self-centralization of a normal three-group with two-group quotient

In a finite solvable group with trivial two-core, a normal three-subgroup
whose quotient is a two-group contains its full centralizer. The subgroup
need not be elementary abelian and no action or graph structure is assumed.

The subgroup is nilpotent and lies in the Fitting subgroup. Conversely,
every prime core lies in it: the two-core is trivial, and every other
prime core has trivial image in the two-group quotient. The prime-core
formula for the Fitting subgroup therefore identifies it with the supplied
three-subgroup. Solvable Fitting self-centralization proves the conclusion.

This is the normal Hall subgroup argument giving faithfulness of the
binary actor on the actual residual image in Stellmacher (8.6)(21),
printed p.45. The native quotient-action transfer supplies the hypotheses.
-/

namespace Subgroup
public theorem centralizer_normal_three_le_of_two_quotient
    {X : Type*} [Group X] [Finite X]
    (hsolv : Group.IsSolvable X) (hcore : pCore 2 X = ⊥)
    (F : Subgroup X) [F.Normal] (hF : IsPGroup 3 F)
    (hquot : IsPGroup 2 (X ⧸ F)) : centralizer (F : Set X) ≤ F := by
  classical
  have hFfit : F ≤ fittingSubgroup X := le_sSup ⟨inferInstance,hF.isNilpotent⟩
  have hfitF : fittingSubgroup X ≤ F := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.val.val = 2
    · rw [hp,hcore]
      exact bot_le
    · let quotient := QuotientGroup.mk' F
      have himageP : IsPGroup p.val.val ((pCore p.val.val X).map quotient) :=
        pCore_isPGroup.map quotient
      have himageTwo : IsPGroup 2 ((pCore p.val.val X).map quotient) :=
        hquot.to_subgroup _
      have hbot : (pCore p.val.val X).map quotient = ⊥ :=
        disjoint_self.mp (IsPGroup.disjoint_of_ne p.val.val 2 hp _ _ himageP himageTwo)
      have hle := (Subgroup.map_eq_bot_iff _).mp hbot
      rwa [QuotientGroup.ker_mk'] at hle
  rw [show F = fittingSubgroup X from le_antisymm hFfit hfitF]
  exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
end Subgroup
