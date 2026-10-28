module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.IsPerfect

/-!
# Prime residuals and perfect images

A finite perfect group has no nontrivial prime-group quotient. Consequently
a homomorphism with perfect image maps the prime residual onto that entire
image. The second assertion uses the literal range and homomorphism.

This standard residual argument is applied to the point normalizer in
Aschbacher–Smith, The Classification of Quasithin Groups, combined manuscript
of 1 March 2004, 13.8.29(1)–(3), printed p.964.
-/

public section
namespace Subgroup
variable {A B : Type*} [Group A] [Group B]

/-- A finite perfect group has no nontrivial prime-group quotient. -/
theorem pResidual_eq_top_of_isPerfect [Finite A] [Group.IsPerfect A]
    (p : ℕ) [Fact p.Prime] : pResidual p A = ⊤ := by
  let : Group.IsNilpotent (A ⧸ pResidual p A) :=
    (isPGroup_quotient_pResidual p).isNilpotent
  have hs : Subsingleton (A ⧸ pResidual p A) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ pResidual p A) inferInstance
  apply top_unique
  intro a _
  exact (QuotientGroup.eq_one_iff a).mp (Subsingleton.elim _ _)

/-- A homomorphism with perfect image has the same image on the prime residual. -/
theorem map_pResidual_eq_range_of_isPerfect [Finite A]
    (p : ℕ) [Fact p.Prime] (f : A →* B) [Group.IsPerfect f.range] :
    (pResidual p A).map f = f.range := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have he := map_pResidual_of_surjective p f.rangeRestrict f.rangeRestrict_surjective
  rw [pResidual_eq_top_of_isPerfect (A := f.range) p] at he
  have hh := congrArg (Subgroup.map f.range.subtype) he
  rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh
end Subgroup
