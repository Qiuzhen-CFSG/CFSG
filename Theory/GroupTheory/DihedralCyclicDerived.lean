module
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Cyclic derived subgroups of the dihedral models

The rotation subgroup is cyclic of index two. The commutative quotient
contains the derived subgroup in that cyclic subgroup. The semidihedral
model uses its literal semidirect-product projection; transport through an
injective homomorphism preserves the conclusion.

Source application: Aschbacher--Smith 2.5.21, printed p.565.
-/
public section
open Subgroup

namespace Theory.GroupTheory
private theorem cyclic_derived_of_cyclic_index_two {P : Type*} [Group P] [Finite P]
    (A : Subgroup P) [IsCyclic A] (hA : A.index=2) : IsCyclic (_root_.commutator P) := by
  let : A.Normal := A.normal_of_index_eq_two hA
  let : IsCyclic (P ⧸ A) := isCyclic_of_prime_card (by simpa only [index] using hA)
  exact isCyclic_of_le (Normal.quotient_commutative_iff_commutator_le.mp
    (inferInstance : IsMulCommutative (P ⧸ A)))

theorem dihedral_derived_cyclic (n : ℕ) [NeZero n] :
    IsCyclic (_root_.commutator (DihedralGroup n)) := by
  let A : Subgroup (DihedralGroup n) := zpowers (DihedralGroup.r 1)
  apply cyclic_derived_of_cyclic_index_two A
  have hc := A.index_mul_card
  have hcA : Nat.card A=n := by
    change Nat.card (zpowers (DihedralGroup.r 1 : DihedralGroup n))=n
    rw [Nat.card_zpowers,DihedralGroup.orderOf_r_one]
  rw [hcA,DihedralGroup.nat_card] at hc
  have hpos : 0<n := NeZero.pos n
  exact Nat.eq_of_mul_eq_mul_right hpos hc

theorem semidihedral_derived_cyclic (n : ℕ) (hn : 4≤n) :
    IsCyclic (_root_.commutator (Semidihedral.StandardModel n hn)) := by
  let Q := Semidihedral.StandardModel n hn
  let A : Subgroup Q :=
    (SemidirectProduct.inl : Multiplicative (ZMod (2^(n-1))) →* Q).range
  let : IsCyclic A := isCyclic_of_surjective
    (SemidirectProduct.inl : Multiplicative (ZMod (2^(n-1))) →* Q).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  apply cyclic_derived_of_cyclic_index_two A
  rw [show A=(SemidirectProduct.rightHom : Q→*Multiplicative (ZMod 2)).ker from
    SemidirectProduct.range_inl_eq_ker_rightHom]
  rw [index_ker,MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective,card_top]
  exact Nat.card_zmod _
end Theory.GroupTheory

namespace Theory.GroupTheory
theorem derived_cyclic_of_injective {P Q : Type*} [Group P] [Group Q]
    (e : P→*Q) (he : Function.Injective e) (hQ : IsCyclic (_root_.commutator Q)) :
    IsCyclic (_root_.commutator P) := by
  have hm : (_root_.commutator P).map e ≤ _root_.commutator Q := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let f : _root_.commutator P →* _root_.commutator Q :=
    (e.comp (_root_.commutator P).subtype).codRestrict _
      (fun a=>hm (mem_map_of_mem e a.property))
  let :=hQ
  exact isCyclic_of_injective f (fun a b h=>Subtype.ext (he (congrArg Subtype.val h)))
end Theory.GroupTheory
