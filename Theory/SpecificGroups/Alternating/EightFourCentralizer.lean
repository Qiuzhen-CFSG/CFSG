module
public import Theory.SpecificGroups.Alternating.FourPairFixer
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic

/-!
# The centralizer of a fixed-point-free A₄ action on eight letters

If an involution of A₄ has no fixed letters, conjugacy of its three
involutions makes every point stabilizer odd. Orbit–stabilizer then forces
all point stabilizers to have order three. They are conjugate and
self-normalizing. Thus restriction to the fixed set of a cubic is faithful
on the commuting permutation group. Four disjoint translates of that fixed
set fit into eight letters, so it has at most two points and its symmetric
group has order at most two.

Only the elementary conjugacy and centralizer calculations in A₄, of order
twelve, use finite certificates. The eight-letter permutations are arbitrary. The subgroup version retains the literal
embedding needed by the normalizer-index obstruction.

Source application: Aschbacher–Smith, the alternating-eight branch of 2.4.32.
-/

public section
namespace AlternatingEight
open Subgroup Equiv MulAction
local notation "A4" => alternatingGroup (Fin 4)
local notation "S8" => Equiv.Perm (Fin 8)

private def cubic : A4 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
  by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private theorem cubic_order : orderOf cubic = 3 := by
  rw [orderOf_eq_prime_iff]
  decide +kernel
private theorem involution_conjugacy : ∀ a b : A4,
    orderOf a = 2 → orderOf b = 2 → ∃ g : A4, g * a * g⁻¹ = b := by
  simp only [orderOf_eq_prime_iff]
  decide +kernel
private theorem cubic_conjugacy : ∀ a : A4, orderOf a = 3 →
    ∃ g : A4, g⁻¹ * cubic * g = a ∨ g⁻¹ * cubic * g = a⁻¹ := by
  simp only [orderOf_eq_prime_iff]
  decide +kernel
private theorem cubic_centralizer : ∀ a : A4, cubic * a = a * cubic →
    a = 1 ∨ a = cubic ∨ a = cubic ^ 2 := by decide +kernel
private def representative : Fin 4 → A4 := ![
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
  ⟨Equiv.swap 1 3 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
  ⟨Equiv.swap 2 3 * Equiv.swap 0 1, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
  1]
private theorem representative_apply : ∀ i : Fin 4, (representative i).val 3 = i := by
  decide +kernel

theorem four_centralizer_card_le_two
    (f : A4 →* S8) (_hf : Function.Injective f)
    (u : A4) (hu : orderOf u = 2) (hfree : ∀ i, f u i ≠ i) :
    Nat.card (centralizer (f.range : Set S8)) ≤ 2 := by
  classical
  let : MulAction A4 (Fin 8) := MulAction.compHom (Fin 8) f
  have hfree' (v : A4) (hv : orderOf v = 2) (i : Fin 8) : f v i ≠ i := by
    obtain ⟨g, hg⟩ := involution_conjugacy u v hu hv
    intro hi
    apply hfree ((f g)⁻¹ i)
    have hh := congrArg (fun j => (f g).symm j) hi
    rw [← hg, map_mul, map_mul, map_inv] at hh
    simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hh
  have hstab (i : Fin 8) : Nat.card (stabilizer A4 i) = 3 := by
    have hodd : ¬ 2 ∣ Nat.card (stabilizer A4 i) := by
      intro hd
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 hd
      have hv' : orderOf (v : A4) = 2 := by simpa using hv
      exact hfree' v hv' i v.property
    have hd : Nat.card (stabilizer A4 i) ∣ 12 := by
      simpa only [alternatingGroup.card_of_card_eq_four (by simp : Nat.card (Fin 4) = 4)]
        using (stabilizer A4 i).card_subgroup_dvd_card
    have hp : Nat.card (orbit A4 i) * Nat.card (stabilizer A4 i) = 12 := by
      rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup A4 i)]
      exact alternatingGroup.card_of_card_eq_four (by simp)
    have hb : Nat.card (orbit A4 i) ≤ 8 := by
      simpa using Nat.card_le_card_of_injective
        (fun x : orbit A4 i => (x : Fin 8)) Subtype.val_injective
    have hb' := Nat.le_of_dvd (by decide : 0 < 12) hd
    interval_cases hs : Nat.card (stabilizer A4 i) <;> simp_all
  let P : Subgroup A4 := zpowers cubic
  have hPcard : Nat.card P = 3 := (Nat.card_zpowers cubic).trans cubic_order
  have hPnatural : P ≤ stabilizer A4 (3 : Fin 4) := by
    apply zpowers_le.mpr
    change cubic.val 3 = 3
    decide +kernel
  have hnormalizer : normalizer (P : Set A4) ≤ P := by
    intro a ha
    have hac := Theory.SpecificGroups.Alternating.FourPairFixer.normalizer_three_le_centralizer
      P hPcard ha
    have hh := mem_centralizer_iff.mp hac cubic (mem_zpowers cubic)
    rcases cubic_centralizer a hh with rfl | rfl | rfl
    · exact P.one_mem
    · exact mem_zpowers cubic
    · exact P.pow_mem (mem_zpowers cubic) 2
  let F := {i : Fin 8 // f cubic i = i}
  have hstabF (x : F) : stabilizer A4 x.val = P := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    rw [hstab, hPcard]
  have hsaturates (i : Fin 8) : ∃ (a : A4) (x : F), f a x.val = i := by
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 3
      (show 3 ∣ Nat.card (stabilizer A4 i) by rw [hstab])
    have hv' : orderOf (v : A4) = 3 := by simpa using hv
    obtain ⟨g, hg⟩ := cubic_conjugacy v hv'
    have hfix : f cubic (f g i) = f g i := by
      apply (f g).symm.injective
      have hvfix : f (v : A4) i = i := v.property
      have hvinvfix : f (v : A4)⁻¹ i = i := by
        rw [map_inv]
        exact (f (v : A4)).symm_apply_eq.mpr hvfix.symm
      have heq : (f g).symm (f cubic (f g i)) = f (g⁻¹ * cubic * g) i := by
        simp only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      rw [heq, Equiv.symm_apply_apply]
      rcases hg with hg | hg
      · rwa [hg]
      · rwa [hg]
    exact ⟨g⁻¹, ⟨f g i, hfix⟩, by simp only [map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply]⟩
  let pack : Fin 4 × F → Fin 8 := fun x => f (representative x.1) x.2.val
  have hpack : Function.Injective pack := by
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    let g : A4 := (representative j)⁻¹ * representative i
    have hgy : g • x.val = y.val := by
      change f g x.val = y.val
      change f (representative i) x.val = f (representative j) y.val at heq
      simp only [g, map_mul, map_inv, Equiv.Perm.mul_apply, heq,
        Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    have hgP : g ∈ P := by
      apply hnormalizer
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hh := stabilizer_smul_eq_stabilizer_map_conj g x.val
      rw [hgy, hstabF x, hstabF y] at hh
      exact hh.symm
    have hij : i = j := by
      have hn := hPnatural hgP
      change (representative j).val⁻¹ ((representative i).val 3) = 3 at hn
      have hh := congrArg (representative j).val hn
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply, representative_apply] using hh
    subst j
    have hxy : x = y := Subtype.ext ((f (representative i)).injective heq)
    subst y
    rfl
  have hFcard : Nat.card F ≤ 2 := by
    have hh := Nat.card_le_card_of_injective pack hpack
    rw [Nat.card_prod, Nat.card_fin, Nat.card_fin] at hh
    omega
  let C := centralizer (f.range : Set S8)
  have hcomm (z : C) (a : A4) (i : Fin 8) : f a (z.val i) = z.val (f a i) :=
    congrArg (fun p : S8 => p i) (mem_centralizer_iff.mp z.property (f a) ⟨a, rfl⟩)
  let restrict : C → Equiv.Perm F := fun z => z.val.subtypePerm (fun i => by
    rw [hcomm]
    exact z.val.injective.eq_iff)
  have hrestrict : Function.Injective restrict := by
    intro z w heq
    apply Subtype.ext
    apply Equiv.ext
    intro i
    obtain ⟨a, x, rfl⟩ := hsaturates i
    rw [← hcomm, ← hcomm]
    apply congrArg (f a)
    exact congrArg (fun p : Equiv.Perm F => (p x).val) heq
  have hb := Nat.card_le_card_of_injective restrict hrestrict
  have hp : Nat.card (Equiv.Perm F) ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
    exact Nat.factorial_le hFcard
  exact hb.trans hp

/-- The literal subgroup form used by the normalizer-index obstruction. -/
theorem four_subgroup_centralizer_card_le_two
    (B : Subgroup S8) (e : B ≃* A4) (u : B)
    (hu : orderOf u = 2) (hfree : ∀ i, u.val i ≠ i) :
    Nat.card (centralizer (B : Set S8)) ≤ 2 := by
  let f : A4 →* S8 := B.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := B.subtype_injective.comp e.symm.injective
  have hr : f.range = B := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (e.symm a).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      change (e.symm (e ⟨x, hx⟩) : S8) = x
      rw [e.symm_apply_apply]
  have hh := four_centralizer_card_le_two f hf (e u) ((e.orderOf_eq u).trans hu)
    (fun i => by simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, Subgroup.coe_subtype] using hfree i)
  rwa [hr] at hh

end AlternatingEight
