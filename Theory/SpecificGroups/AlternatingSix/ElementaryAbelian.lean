module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Fin

/-!
# An elementary abelian subgroup of order nine in A₆

Embed A₃ × A₃ by its actions on two disjoint three-point sets, then relabel
those six points. Injectivity proves the order, and the two cyclic factors
prove the exponent and commutativity. The transport theorem applies to any
actual model of A₆.

This is the elementary model construction used in Aschbacher–Smith 15.4.23
(printed p.1165); no local classification or rank obstruction is used here.
-/

@[expose] public section

open Subgroup Equiv
open scoped IsMulCommutative
namespace alternatingGroup

private abbrev A3 := alternatingGroup (Fin 3)

private def sumHom : A3 × A3 →* alternatingGroup (Fin 3 ⊕ Fin 3) :=
  ((Perm.sumCongrHom (Fin 3) (Fin 3)).comp
    ((alternatingGroup (Fin 3)).subtype.prodMap (alternatingGroup (Fin 3)).subtype)).codRestrict _
      (by
        intro x
        change Perm.sign (Equiv.sumCongr (x.1 : Perm (Fin 3)) (x.2 : Perm (Fin 3))) = 1
        rw [Perm.sign_sumCongr, Perm.mem_alternatingGroup.mp x.1.property,
          Perm.mem_alternatingGroup.mp x.2.property, one_mul])

private def embedding : A3 × A3 →* alternatingGroup (Fin 6) :=
  (Equiv.altCongrHom finSumFinEquiv).toMonoidHom.comp sumHom

private theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  have h' := (Equiv.altCongrHom finSumFinEquiv).injective h
  have h'' := Perm.sumCongrHom_injective (congrArg Subtype.val h')
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h''))
    (Subtype.ext (congrArg Prod.snd h''))

private theorem card_A3 : Nat.card A3 = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The two disjoint three-point actions give an E₉ in A₆. -/
theorem exists_elementaryAbelian_nine : ∃ P : Subgroup (alternatingGroup (Fin 6)),
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 := by
  let f := embedding
  let : IsMulCommutative A3 := alternatingGroup.isMulCommutative_of_card_le_three (by simp)
  have hpow (a : A3) : a ^ 3 = 1 := by
    simpa only [card_A3] using (pow_card_eq_one' (x := a))
  let : IsElementaryAbelian 3 (⊤ : Subgroup (A3 × A3)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by
      intro x
      apply Subtype.ext
      exact Prod.ext (hpow x.val.1) (hpow x.val.2)) }
  refine ⟨(⊤ : Subgroup (A3 × A3)).map f, IsElementaryAbelian.map f, ?_⟩
  rw [Subgroup.card_map_of_injective embedding_injective, Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_prod, card_A3]
/-- Transport the actual E₉ subgroup along a multiplicative equivalence. -/
theorem exists_elementaryAbelian_nine_of_equiv {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 6)) :
    ∃ P : Subgroup H, IsElementaryAbelian 3 P ∧ Nat.card P = 9 := by
  obtain ⟨P, hP, hc⟩ := exists_elementaryAbelian_nine
  let := hP
  refine ⟨P.map e.symm.toMonoidHom, IsElementaryAbelian.map _, ?_⟩
  exact (Subgroup.card_map_of_injective e.symm.injective).trans hc

end alternatingGroup
