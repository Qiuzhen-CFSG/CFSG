module
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupTheory.TwoThreeSolvable
public import GorensteinWalter.PSL2Cardinality

/-!
# Component uniqueness in binary rank-one Sylow overgroups

Proper full-Sylow overgroups in SL₂ in characteristic two are solvable.
For fields of size at least four the whole group is nonabelian simple;
the two-element field gives the solvable group SL₂(2). These facts establish
uniqueness for every binary field, including the endpoint needed in triality.
Source: Aschbacher--Smith A.3.12, pp.47--48.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
/-- Every full-Sylow overgroup has at most one C-component. -/
theorem sylow_overgroup_component_unique : SylowOvergroupComponentUnique SL(2,F) := by
  by_cases hF : 4 ≤ Nat.card F
  · let e := Theory.PSL2.sl2QuotientEquiv F
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
    let : IsSimpleGroup SL(2,F) := e.isSimpleGroup
    let : Group.IsPerfect PSL(2,F) := GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
    let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective
      (f := e.symm.toMonoidHom) e.symm.surjective
    exact SylowOvergroupComponentUnique.of_solvable_proper_overgroups
      isSolvable_of_proper_sylow_overgroup
  · have hc : Nat.card F = 2 := by
      let : Fintype F := Fintype.ofFinite F
      obtain ⟨n,_,hn⟩ := FiniteField.card F 2
      have he : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
      have hpos : 0 < (n : ℕ) := n.pos
      have hn1 : (n : ℕ) = 1 := by
        by_contra hh
        have h4 : 2 ^ 2 ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      simpa [hn1] using he
    let : Group.IsSolvable SL(2,F) := by
      apply isSolvable_of_prime_dvd_card_eq_two_or_three
      intro p hp hd
      rw [GorensteinWalter.sl2_card_formula, hc] at hd
      norm_num at hd
      have hh := hp.dvd_mul.mp (show p ∣ 2 * 3 from hd)
      exact hh.elim
        (fun h => Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
        (fun h => Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one))
    exact SylowOvergroupComponentUnique.of_isSolvable
end Matrix.SpecialLinearGroup

namespace Theory.PSL2
open scoped MatrixGroups
/-- The actual projective quotient in characteristic two. -/
theorem sylow_overgroup_component_unique (F : Type*) [Field F] [Finite F] [CharP F 2] :
    Theory.GroupTheory.SylowOvergroupComponentUnique PSL(2,F) :=
  Theory.GroupTheory.SylowOvergroupComponentUnique.of_equiv (sl2QuotientEquiv F).symm
    (Matrix.SpecialLinearGroup.sylow_overgroup_component_unique F)
end Theory.PSL2
