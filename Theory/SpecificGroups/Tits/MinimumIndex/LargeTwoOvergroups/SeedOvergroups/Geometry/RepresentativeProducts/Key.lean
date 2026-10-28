module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.Membership
/-!
# Conjugation fingerprints for representative products

For a first place the marked object is its central involution; for a second
place it is its four-group. Membership of `a * b⁻¹` forces their conjugates
by `a⁻¹` and `b⁻¹` to agree. Summing three-point fingerprints of the three
nonidentity elements gives a computable invariant of a conjugated four-group.
No injectivity of this sum is asserted or needed.

A selector assigns a place bit to each fingerprint. If every stored row
contains its selected bit, equal fingerprints imply overlapping masks. This
reduces the quadratic product exclusion to linear checks on the stored rows.
Source: the literal Parrott (1972), §5, p.683 words in Geometry.Data, and the
centralizer and normalizer identifications used by Geometry.Membership.
-/

@[expose] public section
open scoped BigOperators
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts
open Subgroup ExceptionalParabolics RelativeParabolicNormalizers
open OuterOddSubgroups.OverlapCentralizers
private theorem val_mul (a b : Atlas1600Group) : (a * b).val = a.val * b.val := rfl
private theorem val_inv (a : Atlas1600Group) : a⁻¹.val = a.val⁻¹ := rfl

def signature (g : Equiv.Perm (Fin 1600)) : Nat :=
  (g 0).val + 1600 * (g 1).val + 1600^2 * (g 2).val

def centerKey (g : Equiv.Perm (Fin 1600)) (second : Bool) : Nat :=
  if second then
    signature (g⁻¹ * centralPerm * g) + signature (g⁻¹ * matePerm * g) +
      signature (g⁻¹ * (centralPerm * matePerm) * g)
  else signature (g⁻¹ * centralPerm * g)

def cosetKey (g : Equiv.Perm (Fin 1600)) (j : Fin 38) : Nat :=
  centerKey ((fastConjugator j)⁻¹ * g) (decide (17 ≤ j.val))

private noncomputable def centerElements : Finset Atlas1600Group :=
  by classical exact {1, atlas1600R5, secondCenterMate, atlas1600R5 * secondCenterMate}

private theorem mem_centerElements (x : Atlas1600Group) :
    x ∈ centerElements ↔ x ∈ secondCenter := by
  classical
  simp only [centerElements, Finset.mem_insert, Finset.mem_singleton, mem_secondCenter_iff]
  exact or_congr_right or_left_comm

private theorem centerElements_sum (f : Atlas1600Group → Nat) :
    ∑ x ∈ centerElements, f x =
      f 1 + f atlas1600R5 + f secondCenterMate + f (atlas1600R5 * secondCenterMate) := by
  classical
  have h (x y : Atlas1600Group) (h : x.val 0 ≠ y.val 0) : x ≠ y := by
    intro he
    exact h (congrArg (fun g : Atlas1600Group => g.val 0) he)
  have h1 : (1 : Atlas1600Group) ≠ atlas1600R5 := h _ _ (by
    change (1 : Equiv.Perm (Fin 1600)) 0 ≠ atlas1600R5.val 0
    rw [← centralPerm_eq]; decide +kernel)
  have h2 : (1 : Atlas1600Group) ≠ secondCenterMate := h _ _ (by
    change (1 : Equiv.Perm (Fin 1600)) 0 ≠ secondCenterMate.val 0
    rw [← matePerm_eq]; decide +kernel)
  have h3 : (1 : Atlas1600Group) ≠ atlas1600R5 * secondCenterMate := h _ _ (by
    change (1 : Equiv.Perm (Fin 1600)) 0 ≠ (atlas1600R5.val * secondCenterMate.val) 0
    rw [← centralPerm_eq, ← matePerm_eq]; decide +kernel)
  have h4 : atlas1600R5 ≠ secondCenterMate := h _ _ (by
    rw [← centralPerm_eq, ← matePerm_eq]; decide +kernel)
  have h5 : atlas1600R5 ≠ atlas1600R5 * secondCenterMate := by
    simpa using h2.symm
  have h6 : secondCenterMate ≠ atlas1600R5 * secondCenterMate := by
    simpa using h1.symm
  simp [centerElements, h1, h2, h3, h4, h5, h6, Nat.add_assoc]

private theorem centerKey_eq_sum (g : Atlas1600Group) :
    signature 1 + centerKey g.val true =
      ∑ x ∈ centerElements, signature (g⁻¹ * x * g).val := by
  rw [centerElements_sum]
  simp only [centerKey, if_true, centralPerm_eq, matePerm_eq]
  change _ = signature (g.val⁻¹ * 1 * g.val) + _ + _ + _
  simp only [mul_one, inv_mul_cancel, Nat.add_assoc, val_mul, val_inv]

private theorem centerKey_eq_of_centralizes (a b : Atlas1600Group)
    (h : a * b⁻¹ ∈ centralizer ({atlas1600R5} : Set Atlas1600Group)) :
    centerKey a.val false = centerKey b.val false := by
  have hc := mem_centralizer_singleton_iff.mp h
  have he : a⁻¹ * atlas1600R5 * a = b⁻¹ * atlas1600R5 * b := by
    calc
      _ = a⁻¹ * (atlas1600R5 * (a * b⁻¹)) * b := by group
      _ = a⁻¹ * ((a * b⁻¹) * atlas1600R5) * b := by rw [hc]
      _ = _ := by group
  simpa only [centerKey, Bool.false_eq_true, if_false, centralPerm_eq, val_mul, val_inv] using
    congrArg (fun x : Atlas1600Group => signature x.val) he

private theorem centerKey_eq_of_normalizes (a b : Atlas1600Group)
    (h : a * b⁻¹ ∈ normalizer (secondCenter : Set Atlas1600Group)) :
    centerKey a.val true = centerKey b.val true := by
  classical
  apply Nat.add_left_cancel (n := signature 1)
  rw [centerKey_eq_sum, centerKey_eq_sum]
  let e := MulAut.conj (a * b⁻¹)
  have he (x : Atlas1600Group) : e x ∈ centerElements ↔ x ∈ centerElements := by
    rw [mem_centerElements, mem_centerElements]
    exact (mem_normalizer_iff.mp h x).symm
  apply Finset.sum_bij (fun x _ => e.symm x)
  · intro x hx
    exact (he (e.symm x)).mp (by simpa using hx)
  · intro x hx y hy heq
    exact e.symm.injective heq
  · intro y hy
    exact ⟨e y, (he y).mpr hy, e.symm_apply_apply y⟩
  · intro x hx
    apply congrArg (fun z : Atlas1600Group => signature z.val)
    change a⁻¹ * x * a = b⁻¹ * ((a * b⁻¹)⁻¹ * x * (a * b⁻¹)) * b
    group

/-- Membership of a*b⁻¹ forces equality of inverse-conjugation fingerprints. -/
theorem cosetKey_eq_of_mem (a b : Atlas1600Group) (j : Fin 38)
    (h : a * b⁻¹ ∈ place j) : cosetKey a.val j = cosetKey b.val j := by
  obtain ⟨c, hc, he⟩ := h
  change c ∈ placeBase j at hc
  let w := placeConjugator j
  have he' : w * c * w⁻¹ = a * b⁻¹ := he
  have hw : w⁻¹ * a * (w⁻¹ * b)⁻¹ = c := by
    calc
      _ = w⁻¹ * (a * b⁻¹) * w := by group
      _ = w⁻¹ * (w * c * w⁻¹) * w := by rw [he']
      _ = c := by group
  simp only [cosetKey, fastConjugator_eq]
  change centerKey (w⁻¹ * a).val _ = centerKey (w⁻¹ * b).val _
  by_cases hj : j.val < 17
  · have hc' : c ∈ centralizer ({atlas1600R5} : Set Atlas1600Group) := by
      simpa only [placeBase, if_pos hj, first_eq_centralizer] using hc
    have hd : decide (17 ≤ j.val) = false := by simp [Nat.not_le.mpr hj]
    rw [hd]
    exact centerKey_eq_of_centralizes _ _ (hw.symm ▸ hc')
  · have hc' : c ∈ normalizer (secondCenter : Set Atlas1600Group) := by
      simpa only [placeBase, if_neg hj,
        second_eq_normalizer_secondCenter first_eq_centralizer] using hc
    have hd : decide (17 ≤ j.val) = true := by simp [Nat.le_of_not_gt hj]
    rw [hd]
    exact centerKey_eq_of_normalizes _ _ (hw.symm ▸ hc')

/-- A common selected mask bit rules out every disjoint-mask product.
The selector is arbitrary; only its checked values on the stored rows matter. -/
theorem excludes_of_selector (t : Fin 18) (select : Fin 38 → Nat → Fin 38)
    (hselect : ∀ r ∈ rows t, ∀ j ∈ placePattern t,
      select j (cosetKey (rowPerm r) j) ∈ placePattern t ∧
      rowMember r (select j (cosetKey (rowPerm r) j)) = true)
    (a : Row) (ha : a ∈ rows t) (b : Row) (hb : b ∈ rows t)
    (hab : sharesPlace t a b = false) (j : Fin 38) (hj : j ∈ placePattern t) :
    placeTest (rowPerm a * (rowPerm b)⁻¹) j = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm : rowElement a * (rowElement b)⁻¹ ∈ place j := by
    apply (placeTest_iff _ _).mp
    simpa only [rowPerm_eq, val_mul, val_inv] using ht
  have hk : cosetKey (rowPerm a) j = cosetKey (rowPerm b) j := by
    simpa only [rowPerm_eq] using cosetKey_eq_of_mem _ _ j hm
  obtain ⟨hka, hma⟩ := hselect a ha j hj
  obtain ⟨_, hmb⟩ := hselect b hb j hj
  rw [← hk] at hmb
  have ht' : sharesPlace t a b = true := by
    exact List.any_eq_true.mpr ⟨_, hka, by simp [hma, hmb]⟩
  rw [hab] at ht'
  contradiction
end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeProducts
