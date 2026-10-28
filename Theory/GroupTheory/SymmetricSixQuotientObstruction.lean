module
public import Theory.Alternating.Aut
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Symmetric-six obstruction in a centralizer quotient

Let a nontrivial normal subgroup K lie in a subgroup C isomorphic to S₆.
Every nontrivial normal subgroup of S₆ contains A₆, whose centralizer in S₆
is trivial. Consequently C embeds under the original quotient by C_J(K).
If H supplements C_J(K), this is the same quotient as H/C_H(K). A quotient
of order 720 containing an element of order eight is therefore impossible:
the embedding of C would be an equivalence, but S₆ has no element of order eight.

This isolates the centralizer obstruction in Aschbacher–Smith, Lemma 2.5.21,
printed p.566 of the combined 1 March 2004 manuscript. The source application
takes C to be the centralizer of a transposition on the actual A₈ overcomponent,
and the quotient to be the original M₁₀ or PGL₂(9) quotient. No choice of an
isomorphism between its contained A₆ and the natural A₆ is required.
-/

public section
namespace Theory.GroupTheory
open Subgroup Equiv

/-- A permutation on six letters cannot have order eight. -/
theorem symmetric_six_order_ne_eight (s : Perm (Fin 6)) : orderOf s ≠ 8 := by
  intro h
  have hd : orderOf s ∣ 4 := by
    rw [← s.lcm_cycleType, Multiset.lcm_dvd]
    intro n hn
    have hnd : n ∣ 8 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have hns : n ≤ s.cycleType.sum := Multiset.le_sum_of_mem hn
    have hsum : s.cycleType.sum ≤ 6 := s.sum_cycleType_le
    have hn6 : n ≤ 6 := hns.trans hsum
    interval_cases n <;> norm_num at hnd <;> norm_num
  norm_num [h] at hd

/-- A centralizer supplement with quotient of order 720 and an element of order
eight cannot contain an S₆ overgroup of the original nontrivial normal subgroup. -/
theorem symmetric_six_quotient_obstruction
    {J Q : Type*} [Group J] [Finite J] [Group Q] [Finite Q]
    (K H C : Subgroup J) [K.Normal] [Nontrivial K]
    (hKC : K ≤ C) (eC : C ≃* Perm (Fin 6))
    (hsupp : H ⊔ centralizer (K : Set J) = ⊤)
    (eQ : (H ⧸ (centralizer (K : Set J)).subgroupOf H) ≃* Q)
    (hcard : Nat.card Q = 720) (h8 : ∃ q : Q, orderOf q = 8) : False := by
  let L := (K.subgroupOf C).map eC.toMonoidHom
  let : L.Normal := (inferInstance : (K.subgroupOf C).Normal).map _ eC.surjective
  have hL : Nontrivial L := by
    apply (nontrivial_iff_exists_ne_one L).mpr
    obtain ⟨k, hk, hk1⟩ := K.exists_ne_one_of_nontrivial
    refine ⟨eC ⟨k, hKC hk⟩, mem_map_of_mem eC.toMonoidHom hk, ?_⟩
    intro he
    exact hk1 (congrArg Subtype.val (eC.map_eq_one_iff.mp he))
  have hAL : alternatingGroup (Fin 6) ≤ L :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) hL
  let Z := centralizer (K : Set J)
  let q := QuotientGroup.mk' Z
  let g : C →* J ⧸ Z := q.comp C.subtype
  have hg : Function.Injective g := by
    apply g.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hxZ : (x : J) ∈ Z := (QuotientGroup.eq_one_iff (N := Z) _).mp hx
    have hxL : eC x ∈ centralizer (L : Set (Perm (Fin 6))) := by
      rintro a ⟨k, hk, rfl⟩
      change eC k * eC x = eC x * eC k
      rw [← map_mul, ← map_mul]
      exact congrArg eC (Subtype.ext (hxZ k hk))
    have hxA := centralizer_le hAL hxL
    rw [_root_.GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide),
      mem_bot] at hxA
    exact mem_bot.mpr (eC.map_eq_one_iff.mp hxA)
  let f : H →* J ⧸ Z := q.comp H.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hmap : H.map q = ⊤ := by
      have h := congrArg (fun A : Subgroup J => A.map q)
        (show H ⊔ Z = ⊤ from hsupp)
      have hZ : Z.map q = ⊥ := QuotientGroup.map_mk'_self Z
      simpa only [Subgroup.map_sup, hZ, sup_bot_eq,
        map_top_of_surjective q (QuotientGroup.mk'_surjective Z)] using h
    rw [MonoidHom.range_comp, H.range_subtype, hmap]
  have hk : f.ker = Z.subgroupOf H := by
    ext x
    exact QuotientGroup.eq_one_iff (N := Z) (x : J)
  let eH : (H ⧸ Z.subgroupOf H) ≃* (J ⧸ Z) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let e : (J ⧸ Z) ≃* Q := eH.symm.trans eQ
  let j : C →* Q := e.toMonoidHom.comp g
  have hCcard : Nat.card C = Nat.card Q := by
    rw [Nat.card_congr eC.toEquiv, hcard, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  let E : C ≃* Q := MulEquiv.ofBijective j
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨e.injective.comp hg, hCcard⟩)
  obtain ⟨a, ha⟩ := h8
  apply symmetric_six_order_ne_eight (eC (E.symm a))
  rw [eC.orderOf_eq, E.symm.orderOf_eq, ha]

end Theory.GroupTheory
