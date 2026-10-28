module
public import Theory.GroupTheory.SpecificGroups.DihedralSubgroupModels
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Dihedral central quotients of noncommutative subgroups

Suppose S has cyclic center and dihedral two-group quotient by its center.
A noncommutative subgroup X whose center maps into the center of S likewise
has cyclic center and a dihedral two-group central quotient, with positive
rotation exponent. This is the algebraic subgroup reduction used for the
enlarged Q-group Sylow geometry in ABG II.3 Lemma 2, article p24.

The subgroup center embeds in the cyclic ambient center. Composing inclusion
with the ambient quotient and dihedral equivalence has kernel exactly Z(X),
so the first isomorphism theorem realizes X/Z(X) as a dihedral subgroup.
The existing subgroup classification makes it cyclic or dihedral. Cyclicity
of a central quotient would make X commutative; this also excludes the
degenerate dihedral parameter one. No centricity hypothesis is imposed.
-/

namespace Subgroup

/-- Cyclic centers and noncyclic dihedral central quotients descend under the stated center inclusion. -/
public theorem exists_dihedral_center_quotient_of_center_le
    {S : Type*} [Group S] [IsCyclic (center S)] {n : ℕ}
    (e : (S ⧸ center S) ≃* DihedralGroup (2 ^ n))
    (X : Subgroup S) (hX : ¬ IsMulCommutative X)
    (hcenter : (center X).map X.subtype ≤ center S) :
    IsCyclic (center X) ∧ ∃ k : ℕ, 1 ≤ k ∧
      Nonempty ((X ⧸ center X) ≃* DihedralGroup (2 ^ k)) := by
  have hcyc : IsCyclic ((center X).map X.subtype) := Subgroup.isCyclic_of_le hcenter
  let := hcyc
  refine ⟨isCyclic_of_injective ((center X).equivMapOfInjective X.subtype
    X.subtype_injective).toMonoidHom
    ((center X).equivMapOfInjective X.subtype X.subtype_injective).injective, ?_⟩
  let q := QuotientGroup.mk' (center S)
  let f : X →* DihedralGroup (2 ^ n) := e.toMonoidHom.comp (q.comp X.subtype)
  have hk : f.ker = center X := by
    ext x
    change e (q (x : S)) = 1 ↔ x ∈ center X
    rw [← e.map_one, e.injective.eq_iff]
    change (QuotientGroup.mk (x : S) : S ⧸ center S) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
    · intro hx
      exact hcenter ⟨x, hx, rfl⟩
  let eX : (X ⧸ center X) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hnc : ¬ IsCyclic (X ⧸ center X) := by
    intro hc
    let := hc
    exact hX (isMulCommutative_of_isCyclic_quotient_center_self X)
  rcases DihedralGroup.subgroup_cyclic_or_dihedral_two_power f.range with hc | ⟨k, ⟨ed⟩⟩
  · let := hc
    exact (hnc (isCyclic_of_injective eX.toMonoidHom eX.injective)).elim
  · refine ⟨k, ?_, ⟨eX.trans ed⟩⟩
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    have hc : IsCyclic (DihedralGroup (2 ^ 0)) := DihedralGroup.isCyclic_iff.mpr (by simp)
    let := hc
    exact hnc (isCyclic_of_injective (eX.trans ed).toMonoidHom (eX.trans ed).injective)

end Subgroup
