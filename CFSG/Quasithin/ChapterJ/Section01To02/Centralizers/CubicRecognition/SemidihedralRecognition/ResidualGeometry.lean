module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.LocalReduction
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.DihedralPresentation
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Basic

/-!
# The actual two-residual and its D8 involution centralizer

The Sylow centralizer surjects onto W/O²(W). Its distinguished involution
therefore has central image; fusion makes the reflection have that same image.
The SD16 relation then kills the squared rotation and the reflection. Thus the
quotient has order at most two, and order-four transfer makes its order two.

In any index-two subgroup, the squared rotation and the reflection generate
the centralizer intersection, which has order eight and the dihedral relations.
Swapping the subgroup restrictions identifies this with the literal involution
centralizer. The already proved index-two fusion adjustment supplies one
involution class inside the residual, giving exactly the hypotheses of I.4.1(2).

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446), and I.4.1(2),
printed p.415 (PDF p.426).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses
variable {W : Type*} [Group W] [Finite W] (h : Hypotheses W)
include h

/-- The actual two-residual has index two, using fusion in its two-group quotient. -/
theorem twoResidual_index : (pResidual 2 W).index = 2 := by
  let R := pResidual 2 W
  let q := QuotientGroup.mk' R
  let f : h.C →* W ⧸ R := q.comp h.C.subtype
  have hf : Function.Surjective f := by
    obtain ⟨S, hS⟩ := h.centralizer_isSylow
    let T := S.mapSurjective (QuotientGroup.mk'_surjective R)
    have hp : IsPGroup 2 (⊤ : Subgroup (W ⧸ R)) :=
      (isPGroup_quotient_pResidual 2).to_subgroup ⊤
    have ht : (T : Subgroup (W ⧸ R)) = ⊤ := top_unique (hp.le_sylow_of_normal T)
    intro x
    have hx : x ∈ (S : Subgroup W).map q := by
      change x ∈ (T : Subgroup (W ⧸ R))
      rw [ht]
      trivial
    obtain ⟨y, hy, he⟩ := hx
    exact ⟨⟨y, hS ▸ hy⟩, he⟩
  have hz : q h.z ∈ center (W ⧸ R) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y, rfl⟩ := hf x
    change q (y : W) * q h.z = q h.z * q (y : W)
    simpa only [map_mul] using congrArg q (mem_centralizer_singleton_iff.mp y.property)
  have hbz : f h.reflection = q h.z :=
    (q.map_isConj (h.involutions_conjugate h.reflection
      ((orderOf_coe _).trans h.reflection_order))).eq_of_right_mem_center hz
  have ha2 : f h.rotation ^ 2 = 1 := by
    have he := congrArg f h.conjugation
    simp only [map_mul, map_inv, map_pow] at he
    have hc : Commute (f h.reflection) (f h.rotation) :=
      (mem_center_iff.mp (hbz ▸ hz) _).symm
    rw [hc.mul_inv_cancel] at he
    have he' : f h.rotation * 1 = f h.rotation * f h.rotation ^ 2 := by
      simpa only [mul_one, ← pow_succ'] using he
    exact (mul_left_cancel he').symm
  have hb : f h.reflection = 1 := by
    rw [hbz, ← h.rotation_four]
    change f (h.rotation ^ 4) = 1
    rw [map_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2, one_pow]
  have hs : Function.Surjective (fun i : Fin 2 => f h.rotation ^ i.val) := by
    intro x
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨i, _, rfl | rfl⟩ := Semidihedral.normal_form _ _ 8 3 (by decide)
      h.rotation_order (h.reflection_order ▸ pow_orderOf_eq_one _) h.conjugation h.generators y
    · exact ⟨⟨i % 2, Nat.mod_lt _ (by decide)⟩, by
        dsimp only
        rw [map_pow, ← pow_eq_pow_mod i ha2]⟩
    · exact ⟨⟨i % 2, Nat.mod_lt _ (by decide)⟩, by
        dsimp only
        rw [map_mul, map_pow, hb, mul_one, ← pow_eq_pow_mod i ha2]⟩
  have hc : Nat.card (W ⧸ R) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Nat.card_le_card_of_surjective _ hs
  have hpos : 0 < R.index := Nat.card_pos
  have hne : R.index ≠ 1 := by
    intro he
    exact h.twoResidual_ne_top (Subgroup.index_eq_one.mp he)
  change R.index ≤ 2 at hc
  change R.index = 2
  omega

/-- Every index-two subgroup meets the SD16 centralizer in its dihedral subgroup. -/
theorem index_two_centralizer_model (N : Subgroup W) (hi : N.index = 2) :
    Nonempty (N.subgroupOf h.C ≃* DihedralGroup 4) := by
  let : N.Normal := N.normal_of_index_eq_two hi
  let D := N.subgroupOf h.C
  have hiD : D.index = 2 := by
    have hd : D.index ∣ 2 := hi ▸ N.relIndex_dvd_index_of_normal h.C
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
    · exact False.elim (h.centralizer_not_le_of_index_two N hi (relIndex_eq_one.mp he))
    · exact he
  have hcD : Nat.card D = 8 := by
    have hc := D.card_mul_index
    rw [hiD, h.centralizer_card] at hc
    omega
  have haN : ((h.rotation ^ 2 : h.C) : W) ∈ N :=
    N.sq_mem_of_index_two hi h.rotation
  have hbN : (h.reflection : W) ∈ N := h.involution_mem_of_index_two N hi _
    ((orderOf_coe _).trans h.reflection_order)
  have hanN : (h.rotation : W) ∉ N := by
    intro ha
    apply h.centralizer_not_le_of_index_two N hi
    have ht : N.subgroupOf h.C = ⊤ := top_unique (by
      rw [← h.generators]
      apply (closure_le _).mpr
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨ha, hbN⟩)
    exact subgroupOf_eq_top.mp ht
  let a : D := ⟨h.rotation ^ 2, haN⟩
  let b : D := ⟨h.reflection, hbN⟩
  have heven (i : ℕ) (hiN : ((h.rotation ^ i : h.C) : W) ∈ N) : i % 2 = 0 := by
    have he : h.rotation ^ i = (h.rotation ^ 2) ^ (i / 2) * h.rotation ^ (i % 2) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [he, coe_mul] at hiN
    have hm : ((h.rotation ^ (i % 2) : h.C) : W) ∈ N :=
      (N.mul_mem_cancel_left (N.pow_mem haN (i / 2))).mp hiN
    have hmod := Nat.mod_lt i (by decide : 0 < 2)
    by_contra hn
    have hmodone : i % 2 = 1 := by omega
    rw [hmodone, pow_one] at hm
    exact hanN hm
  have hg : closure ({a, b} : Set D) = ⊤ := by
    apply top_unique
    intro x _
    have hbb : h.reflection ^ 2 = 1 := h.reflection_order ▸ pow_orderOf_eq_one _
    obtain ⟨i, _, he | he⟩ := Semidihedral.normal_form _ _ 8 3 (by decide)
      h.rotation_order hbb h.conjugation h.generators (x : h.C)
    · have hiN : ((h.rotation ^ i : h.C) : W) ∈ N := he ▸ x.property
      have heq : i = 2 * (i / 2) := by have := heven i hiN; omega
      have hx : x = a ^ (i / 2) := by
        apply Subtype.ext
        change (x : h.C) = (h.rotation ^ 2) ^ (i / 2)
        rw [he, ← pow_mul, ← heq]
      rw [hx]
      exact pow_mem (subset_closure (by simp)) _
    · have hiN : ((h.rotation ^ i : h.C) : W) ∈ N := by
        have hm : ((h.rotation ^ i * h.reflection : h.C) : W) ∈ N := he ▸ x.property
        exact (N.mul_mem_cancel_right hbN).mp hm
      have heq : i = 2 * (i / 2) := by have := heven i hiN; omega
      have hx : x = a ^ (i / 2) * b := by
        apply Subtype.ext
        change (x : h.C) = (h.rotation ^ 2) ^ (i / 2) * h.reflection
        rw [he, ← pow_mul, ← heq]
      rw [hx]
      exact mul_mem (pow_mem (subset_closure (by simp)) _) (subset_closure (by simp))
  apply dihedralGroup_equiv_of_relations (by decide) a b _ _ _ hg hcD
  · apply Subtype.ext
    change (h.rotation ^ 2) ^ 4 = 1
    rw [← pow_mul]
    change h.rotation ^ 8 = 1
    rw [← h.rotation_order, pow_orderOf_eq_one]
  · apply Subtype.ext
    exact h.reflection_order ▸ pow_orderOf_eq_one _
  · apply Subtype.ext
    change h.reflection * h.rotation ^ 2 * h.reflection⁻¹ = (h.rotation ^ 2)⁻¹
    rw [← conj_pow, h.conjugation, ← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add]
    change h.rotation ^ 8 = 1
    rw [← h.rotation_order, pow_orderOf_eq_one]

/-- The original distinguished involution, restricted to an index-two subgroup. -/
def indexTwoInvolution (N : Subgroup W) (hi : N.index = 2) : N :=
  ⟨h.z, h.involution_mem_of_index_two N hi h.z h.z_order⟩

/-- Swapping the two restrictions identifies the literal involution centralizer. -/
def indexTwoCentralizerEquiv (N : Subgroup W) (hi : N.index = 2) :
    centralizer ({h.indexTwoInvolution N hi} : Set N) ≃* N.subgroupOf h.C where
  toFun x := ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The actual two-residual satisfies precisely the D8 case of I.4.1. -/
def residualDihedralHypotheses : DihedralInvolutionCentralizerHypotheses (pResidual 2 W) 3 where
  two_le := by decide
  z := h.indexTwoInvolution _ h.twoResidual_index
  involution := by
    have ho : orderOf (h.indexTwoInvolution _ h.twoResidual_index) = 2 :=
      (orderOf_coe _).symm.trans h.z_order
    have hs := pow_orderOf_eq_one (h.indexTwoInvolution _ h.twoResidual_index)
    rw [ho] at hs
    refine ⟨?_, hs⟩
    intro he
    rw [he, orderOf_one] at ho
    omega
  involutions_conjugate x hx := isConj_iff.mp
    (h.involutions_conjugate_in_index_two _ h.twoResidual_index x
      (orderOf_eq_prime hx.2 hx.1))
  centralizer_equiv := ⟨(h.indexTwoCentralizerEquiv _ h.twoResidual_index).trans
    (h.index_two_centralizer_model _ h.twoResidual_index).some⟩

end CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses
