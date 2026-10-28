module
public import Theory.GroupTheory.PGroup.NoNormalFourIndex
public import Theory.GroupTheory.CyclicIndexTwoTransfer
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.PGroup.MultipleNormalFourSylow
public import Theory.GroupTheory.DihedralInvolutionLift

/-!
# Cyclic Sylow reduction in rank-two involution fusion

A cyclic subgroup of index at most two in a Sylow two-subgroup contains
representatives of every ambient involution class by Thompson transfer.
Its unique involution therefore fuses all ambient involutions. Absence of a
normal four supplies such a cyclic subgroup. In a finite simple group of
Sylow rank at most two, two distinct normal fours give a dihedral Sylow
subgroup of order eight and hence the same conclusion.

Source: GLS, volume 2, Lemmas 10.11 and 15.17(ii), and volume 4,
Chapter 1, Lemma 4.10, on the finite simple source domain. The cyclic
transfer and dihedral recognition results are reused without extra inputs.
-/

open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_order_two {x y : G} (h : IsConj x y) (hx : orderOf x = 2) :
    orderOf y = 2 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq x).trans hx

public theorem isConj_involutions_of_cyclic_index_le_two
    (S : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (A : Subgroup S) [IsCyclic A] (hi : A.index ≤ 2)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨s, hs⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  have hso : orderOf s = 2 := (orderOf_coe s).symm.trans (conjugate_order_two hs hx)
  have hi0 := A.index_ne_zero_of_finite
  have hi' : A.index = 1 ∨ A.index = 2 := by omega
  rcases hi' with h1 | h2
  · let : IsCyclic S := isCyclic_of_surjective A.subtype
      (fun a => ⟨⟨a, index_eq_one.mp h1 ▸ mem_top a⟩, rfl⟩)
    obtain ⟨t, ht⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hy)
    have hto : orderOf t = 2 := (orderOf_coe t).symm.trans (conjugate_order_two ht hy)
    have hst : s = t := IsCyclic.eq_of_orderOf_eq_two hso hto
    exact hs.trans (hst ▸ ht.symm)
  · obtain ⟨b, hb, hbA⟩ := S.exists_isConj_mem_of_index_two hno A h2 s hso
    let a : A := ⟨b, hbA⟩
    have hao : orderOf a = 2 := by
      rw [← orderOf_coe, ← orderOf_coe]
      exact conjugate_order_two (hs.trans hb) hx
    have hf := S.involutions_conjugate_of_cyclic_index_two A h2 hno a hao
    exact (hf x hx).trans (hf y hy).symm

public theorem isConj_involutions_of_no_normal_four
    (S : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hfour : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 4)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨A, hAn, hAc, hC⟩ :=
    S.isPGroup'.exists_cyclic_normal_selfCentralizing_of_no_normal_four hfour
  let : A.Normal := hAn
  let : IsCyclic A := hAc
  exact S.isConj_involutions_of_cyclic_index_le_two hno A
    (S.isPGroup'.index_le_two_of_cyclic_normal_selfCentralizing_of_no_normal_four hfour A hC.le)
    x y hx hy

public theorem isConj_involutions_of_distinct_normal_fours [IsSimpleGroup G]
    (S : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup S) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨e⟩ := S.dihedral_of_distinct_normal_fours_of_sylow_rank hrank E F hE hF hne
  let A := DihedralGroup.rotationPreimage e.toMonoidHom
  let f : A →* zpowers (DihedralGroup.r 1 : DihedralGroup 4) :=
    { toFun := fun a => ⟨e a, a.property⟩
      map_one' := Subtype.ext e.map_one
      map_mul' := fun a b => Subtype.ext (e.map_mul a b) }
  let : IsCyclic A := isCyclic_of_injective f (by
    intro a b h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)))
  exact S.isConj_involutions_of_cyclic_index_le_two hno A
    (DihedralGroup.rotationPreimage_index e.toMonoidHom e.surjective).le x y hx hy
end Sylow
