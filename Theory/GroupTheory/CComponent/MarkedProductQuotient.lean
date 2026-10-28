module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# A marked simple factor in a two-core quotient

Given an equivalence G/O₂(G) ≃ A × B with B simple and perfect, the
C-component correspondence lifts the specified second factor to a genuine
C-component of G. Its image is exactly 1 × B under the given quotient map;
no new or unmarked product decomposition is chosen.

This is the standard solvable-kernel component correspondence of
Aschbacher–Smith A.3.3, used in 13.8.25, printed pp.959–960 of the
combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace Subgroup

private def rightFactorEquiv (A B : Type*) [Group A] [Group B] :
    ((⊥ : Subgroup A).prod (⊤ : Subgroup B)) ≃* B where
  toFun x := x.val.2
  invFun y := ⟨(1, y), ⟨one_mem _, mem_top _⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (mem_bot.mp x.property.1).symm rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {A B J : Type*} [Group A] [Group B] [Group J] [Finite J]

/-- Lift the specified simple perfect factor, keeping its exact image under
the given two-core quotient equivalence. -/
theorem exists_cComponent_over_right_factor [IsSimpleGroup B] [Group.IsPerfect B]
    (e : (J ⧸ pCore 2 J) ≃* A × B) :
    ∃ D : Subgroup J, D.IsCComponent ∧
      D.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))) =
        (⊥ : Subgroup A).prod ⊤ := by
  let R := (⊥ : Subgroup A).prod (⊤ : Subgroup B)
  let r := rightFactorEquiv A B
  let : IsSimpleGroup R := r.isSimpleGroup
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := r.symm.toMonoidHom) r.symm.surjective
  have hR : R.IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect (inferInstance : R.Normal).isSubnormal
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  obtain ⟨D, hD, he⟩ := (hR.map_equiv e.symm).exists_map_quotient_eq (pCore 2 J)
  refine ⟨D, hD, ?_⟩
  rw [← map_map, he, map_map]
  simp [R]


end Subgroup

end
