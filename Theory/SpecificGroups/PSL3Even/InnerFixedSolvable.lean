module

public import Theory.SpecificGroups.PSL3Even.ResidualComparison
public import Theory.GroupAction.PerfectCentralQuotient
/-!
# Solvable fixed subgroups of inner involutions in binary PSL₃

The concrete root-centralizer calculation gives solvability for every binary
field, including F₂. Transport preserves the actual fixed subgroup and the
inner involution. For a perfect central cover, the induced quotient action
is faithful; its fixed subgroup has a central kernel, so solvability lifts.

Source application: Aschbacher–Smith 1.1.5(3) and 14.2.15, printed
pp.501–503 and 985–986. The field and central quotient are the actual models.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Even
variable {E : Type*} [Group E]

/-- An inner involution on an actual binary PSL₃ model has solvable fixed group. -/
theorem inner_fixed_solvable (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (a : MulAut E)
    (ha : orderOf a = 2) (hi : ∃ x, a = MulAut.conj x)
    (e : E ≃* PSL(3,F)) : Group.IsSolvable a.fixedSubgroup := by
  let b := MulAut.congr e a
  obtain ⟨d⟩ := ResidualComparison.inner_fixed_equiv_root F hn hF b
    (((MulAut.congr e).orderOf_eq a).trans ha) ((MulAut.congr_inner_iff e a).mpr hi)
  let := ResidualComparison.root_centralizer_solvable F hn hF
  let f := (MulAut.fixedSubgroupCongr e a).trans d
  exact Group.isSolvable_of_surjective (f := f.symm.toMonoidHom) f.symm.surjective

/-- The same fixed-group conclusion holds for a perfect central cover. -/
theorem central_cover_inner_fixed_solvable [Group.IsPerfect E]
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (a : MulAut E)
    (ha : orderOf a = 2) (hi : ∃ x, a = MulAut.conj x)
    (e : E ⧸ center E ≃* PSL(3,F)) : Group.IsSolvable a.fixedSubgroup := by
  let b := MulAut.centralQuotientAction e a
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) a).trans ha
  let := inner_fixed_solvable F hn hF b hb
    ((MulAut.centralQuotientAction_inner_iff e a).mpr hi) (MulEquiv.refl _)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  let g : a.fixedSubgroup →* b.fixedSubgroup :=
    (f.comp a.fixedSubgroup.subtype).codRestrict _ (by
      intro x
      rw [MulAut.mem_fixedSubgroup]
      change b (e (QuotientGroup.mk' (center E) x.val)) = _
      rw [MulAut.centralQuotientAction_apply,
        (MulAut.mem_fixedSubgroup _ _).mp x.property]
      rfl)
  have hk (x : g.ker) : (x.val.val : E) ∈ center E := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    exact (congrArg Subtype.val x.property).trans e.map_one.symm
  let j : g.ker →* center E :=
    (a.fixedSubgroup.subtype.comp g.ker.subtype).codRestrict _ hk
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center E => (z : E)) h
  let : Group.IsSolvable (center E) := Group.isSolvable_of_comm fun x y =>
    Subtype.ext ((mem_center_iff.mp x.property y).symm)
  let : Group.IsSolvable g.ker := Group.isSolvable_of_isSolvable_injective (f := j) hj
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by simp)
end Matrix.PSL3Even
