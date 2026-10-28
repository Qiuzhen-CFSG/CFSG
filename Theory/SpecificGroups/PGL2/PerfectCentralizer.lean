module
public import Theory.SpecificGroups.PGL2.NoncommutativeCentralizer
public import Mathlib.GroupTheory.IsPerfect
/-!
# Perfect subgroups have trivial centralizer in PGL₂

Lift the subgroup to GL₂. An element centralizing its projective image
commutes with the derived subgroup of the lift, by the three-subgroups
lemma across the scalar kernel. That derived subgroup still maps onto
the original nontrivial perfect group and is noncommutative. Its GL₂
centralizer is scalar, hence trivial in PGL₂.
Source application: Aschbacher–Smith C.5.12, printed p.163, prime PSL₂ row.
-/
public section
open Matrix Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.PGL2
variable {F : Type*} [Field F]
theorem centralizer_eq_bot_of_perfect (D : Subgroup (PGL(2,F))) [Group.IsPerfect D] (hne : D ≠ ⊥) :
    centralizer (D : Set (PGL(2,F))) = ⊥ := by
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hne
  let q : GL (Fin 2) F →* PGL(2,F) := ProjGenLinGroup.mk
  let E := D.comap q
  have hmap : E.map q = D := map_comap_eq_self_of_surjective ProjGenLinGroup.mk_surjective D
  have hder : (⁅E,E⁆).map q = D := by rw [map_commutator,hmap,D.commutator_eq_self]
  have hnon : ¬ IsMulCommutative (⁅E,E⁆ : Subgroup (GL (Fin 2) F)) := by
    intro h
    let := h
    have hs : Group.IsSolvable ((⁅E,E⁆).map q) :=
      Group.isSolvable_of_surjective (f := q.subgroupMap ⁅E,E⁆) (q.subgroupMap_surjective _)
    rw [hder] at hs
    exact Group.IsPerfect.not_isSolvable D hs
  apply bot_unique
  intro a ha
  obtain ⟨A,rfl⟩ := ProjGenLinGroup.mk_surjective a
  let P := zpowers A
  have hcomm : ⁅E,P⁆ ≤ center (GL (Fin 2) F) := by
    rw [← ProjGenLinGroup.ker_mk]
    change ⁅E,P⁆ ≤ q.ker
    rw [← Subgroup.map_eq_bot_iff,map_commutator,hmap,MonoidHom.map_zpowers]
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr ha)
  have hderP : ⁅⁅E,E⁆,P⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · exact commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans (center_le_centralizer _))
    · rw [commutator_comm P E]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans (center_le_centralizer _))
  have hA : A ∈ centralizer ((⁅E,E⁆ : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) := by
    apply (commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] at hderP))
    exact mem_zpowers A
  obtain ⟨u,hu⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative ⁅E,E⁆ hnon hA
  change ProjGenLinGroup.mk A = 1
  rw [← hu,ProjGenLinGroup.mk_scalar]
end Theory.PGL2
