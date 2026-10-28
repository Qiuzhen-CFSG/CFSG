module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic
/-!
# Reflections in the actual three-normalizers of A6

The two order-three cycle types are represented by (012) and (012)(345).
Small kernel-checked permutation calculations give normalizer order eighteen
and an inverting involution t. Every normalizer element is either the identity,
an inverting involution, or t times an inverting involution. Conjugation
transports these statements to every order-three element of the actual A6.
The local application uses this coverage to choose a reflection outside N(F).

The cycle-type transport follows the argument already used in
`FusedNine/ComplementFusion.lean`; its private helpers are repeated here to
avoid changing the widely imported fusion module.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 8, Lemma 17, p.16;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup Equiv Equiv.Perm
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.ReflectionChoice

/-- Normalizing a cyclic subgroup of order three means fixing or inverting its generator. -/
public theorem normalizes_three_iff {A : Type*} [Group A] (x y : A) (hx : orderOf x = 3) :
    y ∈ normalizer (zpowers x : Set A) ↔ y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹ := by
  classical
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx2 : x ^ 2 = x⁻¹ := eq_inv_iff_mul_eq_one.mpr (by simpa only [← pow_succ] using hx3)
  constructor
  · intro hy
    have hm := (mem_normalizer_iff.mp hy x).mp (mem_zpowers x)
    have hf : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hx3⟩
    rw [hf.mem_zpowers_iff_mem_range_orderOf, hx] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hil := Finset.mem_range.mp hi
    have his : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases his with rfl | rfl | rfl
    · have hx1 : x = 1 := (MulAut.conj y).injective (by simpa using he.symm)
      simp [hx1] at hx
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (he.symm.trans hx2)
  · intro hy
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (y * x * y⁻¹) = zpowers x
    rcases hy with hy | hy
    · rw [hy]
    · rw [hy, zpowers_inv]

private theorem inverter_ne_one {A : Type*} [Group A] (x t : A)
    (hx : orderOf x = 3) (ht : t * x * t⁻¹ = x⁻¹) : t ≠ 1 := by
  intro he
  have hxinv : x = x⁻¹ := by simpa [he] using ht
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact eq_inv_iff_mul_eq_one.mp hxinv
  have hd := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at hd
  norm_num at hd

private def r₁ : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide +kernel⟩
private def r₂ : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5), by rw [mem_alternatingGroup]; decide +kernel⟩
private def t : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 3 4, by rw [mem_alternatingGroup]; decide +kernel⟩
private def representative (i : Bool) : alternatingGroup (Fin 6) := if i then r₂ else r₁

private theorem alternating_conj_of_odd_centralizer
    {x y : alternatingGroup (Fin 6)} (s : Perm (Fin 6))
    (hs : sign s = -1) (hc : s * (x : Perm (Fin 6)) * s⁻¹ = x)
    (hxy : IsConj (x : Perm (Fin 6)) (y : Perm (Fin 6))) : IsConj x y := by
  obtain ⟨p, hp⟩ := isConj_iff.mp hxy
  by_cases hpe : p ∈ alternatingGroup (Fin 6)
  · exact isConj_iff.mpr ⟨⟨p, hpe⟩, Subtype.ext hp⟩
  · have hps : sign p = -1 := by
      rcases Int.units_eq_one_or (sign p) with h | h
      · exact (hpe (mem_alternatingGroup.mpr h)).elim
      · exact h
    have hqe : p * s ∈ alternatingGroup (Fin 6) := by
      rw [mem_alternatingGroup, map_mul, hps, hs]
      norm_num
    apply isConj_iff.mpr
    refine ⟨⟨p * s, hqe⟩, Subtype.ext ?_⟩
    change (p * s) * (x : Perm (Fin 6)) * (p * s)⁻¹ = (y : Perm (Fin 6))
    calc
      _ = p * (s * (x : Perm (Fin 6)) * s⁻¹) * p⁻¹ := by group
      _ = (y : Perm (Fin 6)) := by rw [hc, hp]

private theorem three_classes (x : alternatingGroup (Fin 6)) (hx : orderOf x = 3) :
    ∃ i, IsConj (representative i) x := by
  have h : ∀ x : alternatingGroup (Fin 6), x ^ 3 = 1 → x ≠ 1 →
      (x : Perm (Fin 6)).cycleType = {3} ∨ (x : Perm (Fin 6)).cycleType = {3, 3} := by
    decide +kernel
  rcases h x (hx ▸ pow_orderOf_eq_one x) (by intro he; simp [he] at hx) with h | h
  · refine ⟨false, ?_⟩
    apply alternating_conj_of_odd_centralizer (swap 3 4) (by decide +kernel) (by decide +kernel)
    apply isConj_iff_cycleType_eq.mpr
    exact (show (r₁ : Perm (Fin 6)).cycleType = {3} from by decide +kernel).trans h.symm
  · refine ⟨true, ?_⟩
    apply alternating_conj_of_odd_centralizer (swap 0 3 * swap 1 4 * swap 2 5)
      (by decide +kernel) (by decide +kernel)
    apply isConj_iff_cycleType_eq.mpr
    exact (show (r₂ : Perm (Fin 6)).cycleType = {3, 3} from by decide +kernel).trans h.symm

private theorem representative_count : ∀ i : Bool,
    Fintype.card {y : alternatingGroup (Fin 6) //
      y * representative i * y⁻¹ = representative i ∨
      y * representative i * y⁻¹ = (representative i)⁻¹} = 18 := by
  decide +kernel

private theorem representative_geometry : ∀ i : Bool,
    t ^ 2 = 1 ∧ t * representative i * t⁻¹ = (representative i)⁻¹ ∧
      ∀ y : alternatingGroup (Fin 6),
        y * representative i * y⁻¹ = representative i ∨
        y * representative i * y⁻¹ = (representative i)⁻¹ →
        (y ^ 2 = 1 ∧ (y = 1 ∨ y * representative i * y⁻¹ = (representative i)⁻¹)) ∨
        ((t * y) ^ 2 = 1 ∧ t * y * representative i * (t * y)⁻¹ = (representative i)⁻¹) := by
  intro i
  cases i <;> simp only [representative, Bool.false_eq_true, ↓reduceIte] <;> decide +kernel

private theorem representative_facts (i : Bool) (hi : orderOf (representative i) = 3) :
    Nat.card (normalizer (zpowers (representative i) : Set (alternatingGroup (Fin 6)))) = 18 ∧
    ∃ t₀ : alternatingGroup (Fin 6), orderOf t₀ = 2 ∧
      t₀ * representative i * t₀⁻¹ = (representative i)⁻¹ ∧
      ∀ y ∈ normalizer (zpowers (representative i) : Set (alternatingGroup (Fin 6))),
        y = 1 ∨ (orderOf y = 2 ∧ y * representative i * y⁻¹ = (representative i)⁻¹) ∨
          (orderOf (t₀ * y) = 2 ∧ t₀ * y * representative i * (t₀ * y)⁻¹ = (representative i)⁻¹) := by
  constructor
  · change Nat.card {y // y ∈ normalizer (zpowers (representative i) : Set (alternatingGroup (Fin 6)))} = 18
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun y => normalizes_three_iff (representative i) y hi)),
      Nat.card_eq_fintype_card]
    exact representative_count i
  · obtain ⟨ht2, htinv, hy⟩ := representative_geometry i
    refine ⟨t, orderOf_eq_prime ht2 (inverter_ne_one _ _ hi htinv), htinv, ?_⟩
    intro y hyn
    rcases hy y ((normalizes_three_iff _ _ hi).mp hyn) with ⟨hy2, rfl | hyinv⟩ | ⟨hy2, hyinv⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨orderOf_eq_prime hy2 (inverter_ne_one _ _ hi hyinv), hyinv⟩)
    · exact Or.inr (Or.inr ⟨orderOf_eq_prime hy2 (inverter_ne_one _ _ hi hyinv), hyinv⟩)

/-- The actual A6 normalizer has order eighteen and is generated by inverting involutions. -/
public theorem a6_three_normalizer (x : alternatingGroup (Fin 6)) (hx : orderOf x = 3) :
    Nat.card (normalizer (zpowers x : Set (alternatingGroup (Fin 6)))) = 18 ∧
    ∃ t₀ : alternatingGroup (Fin 6), orderOf t₀ = 2 ∧ t₀ * x * t₀⁻¹ = x⁻¹ ∧
      ∀ y ∈ normalizer (zpowers x : Set (alternatingGroup (Fin 6))),
        y = 1 ∨ (orderOf y = 2 ∧ y * x * y⁻¹ = x⁻¹) ∨
          (orderOf (t₀ * y) = 2 ∧ t₀ * y * x * (t₀ * y)⁻¹ = x⁻¹) := by
  obtain ⟨i, g, hg⟩ := (three_classes x hx).imp (fun _ h => isConj_iff.mp h)
  let α := MulAut.conj g
  have he : α (representative i) = x := hg
  have hi : orderOf (representative i) = 3 := by rw [← α.orderOf_eq, he, hx]
  obtain ⟨hcard, t₀, ht2, htinv, hy⟩ := representative_facts i hi
  have hmap : (normalizer (zpowers (representative i) : Set (alternatingGroup (Fin 6)))).map α.toMonoidHom =
      normalizer (zpowers x : Set (alternatingGroup (Fin 6))) := by
    rw [map_equiv_normalizer_eq, MonoidHom.map_zpowers]
    change normalizer (zpowers (α (representative i)) : Set (alternatingGroup (Fin 6))) = _
    rw [he]
  refine ⟨?_, α t₀, (α.orderOf_eq t₀).trans ht2, ?_, ?_⟩
  · rw [← hmap, card_map_of_injective α.injective, hcard]
  · simpa only [map_mul, map_inv, he] using congrArg α htinv
  · intro y hyn
    have hym : α.symm y ∈ normalizer (zpowers (representative i) : Set (alternatingGroup (Fin 6))) := by
      rw [← hmap] at hyn
      exact (mem_map_equiv).mp hyn
    rcases hy (α.symm y) hym with hy1 | ⟨hyo, hyi⟩ | ⟨hyo, hyi⟩
    · exact Or.inl (by simpa using congrArg α hy1)
    · exact Or.inr (Or.inl ⟨by simpa using hyo, by simpa only [map_mul, map_inv, he, α.apply_symm_apply] using congrArg α hyi⟩)
    · exact Or.inr (Or.inr ⟨by simpa only [map_mul, α.apply_symm_apply] using (α.orderOf_eq (t₀ * α.symm y)).trans hyo,
        by simpa only [map_mul, map_inv, he, α.apply_symm_apply] using congrArg α hyi⟩)

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.ReflectionChoice
