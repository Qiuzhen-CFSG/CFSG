module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.Presentation
public import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module

/-!
# The five central relation cycles for Rudvalis max4

Normal-closure generation writes every element of the kernel of F/[F,R] → F/R
as a product of the seven central relators. The two exponent maps vanish on
the derived subgroup. Solving their integral equations leaves five explicit
cycles. One is the square of a lift of the original marked generator.

This reduces the local cover calculation to relations between these cycles;
no multiplier bound or presentation completeness is assumed here.
Source: Aschbacher--Smith I.1.3(1), p.407, and the literal words in `Presentation`.
The normal-closure argument follows the existing symplectic-six central
collection implementation.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation
namespace CentralKernel
open scoped IsMulCommutative

def centralRelator (i : Fin 7) : Subgroup.center Central :=
  ⟨toCentral (relator i), centralProjection_ker_le_center (by
    change toPresented (relator i) = 1
    exact toPresented_relator i)⟩

theorem centralRelator_val (i : Fin 7) :
    (centralRelator i : Central) = word (centralGenerator false) (centralGenerator true) i :=
  map_word toCentral _ _ i

def collect (n : Fin 7 → ℤ) : Subgroup.center Central :=
  centralRelator 0 ^ n 0 * centralRelator 1 ^ n 1 * centralRelator 2 ^ n 2 *
    centralRelator 3 ^ n 3 * centralRelator 4 ^ n 4 * centralRelator 5 ^ n 5 *
    centralRelator 6 ^ n 6

@[simp] theorem collect_zero : collect 0 = 1 := by simp [collect]

theorem collect_add (m n : Fin 7 → ℤ) : collect (m + n) = collect m * collect n := by
  simp only [collect, Pi.add_apply, zpow_add]
  ac_rfl

def collectionHom : Multiplicative (Fin 7 → ℤ) →* Central where
  toFun n := (collect n.toAdd : Central)
  map_one' := congrArg Subtype.val collect_zero
  map_mul' m n := congrArg Subtype.val (collect_add m.toAdd n.toAdd)

theorem centralRelator_mem_collection_range (i : Fin 7) :
    (centralRelator i : Central) ∈ collectionHom.range := by
  refine ⟨Multiplicative.ofAdd (fun j => if j = i then 1 else 0), ?_⟩
  fin_cases i <;> simp [collectionHom, collect]

theorem kernel_eq_collection_range : centralProjection.ker = collectionHom.range := by
  have hr : collectionHom.range ≤ Subgroup.center Central := by
    rintro _ ⟨n, rfl⟩
    exact (collect n.toAdd).property
  have : collectionHom.range.Normal := ⟨fun a ha b => by
    simpa [Subgroup.mem_center_iff.mp (hr ha) b, mul_assoc] using ha⟩
  have hR : relations ≤ collectionHom.range.comap toCentral := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, rfl⟩
    exact centralRelator_mem_collection_range i
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective centralRelations x
    exact hR ((toPresented_eq_one_iff w).mp hx)
  · rintro _ ⟨n, rfl⟩
    change centralProjection (collect n.toAdd : Central) = 1
    simp [collect, centralRelator, toPresented_relator]

theorem kernel_normal_form {x : Central} (hx : centralProjection x = 1) :
    ∃ n : Fin 7 → ℤ, x = (collect n : Central) := by
  have hx' : x ∈ collectionHom.range := kernel_eq_collection_range ▸ hx
  obtain ⟨n, rfl⟩ := hx'
  exact ⟨n.toAdd, rfl⟩

def exponent (i : Bool) : Central →* Multiplicative ℤ :=
  descend (FreeGroup.lift (fun j => Multiplicative.ofAdd (if j = i then 1 else 0)))
    (by intro j; rw [CommGroup.center_eq_top]; trivial)

def exponentVector (i : Bool) : Fin 7 → ℤ :=
  if i then ![0, 3, 0, -14, -6, 9, 8] else ![2, 0, 8, 14, 26, 27, 32]

theorem exponent_centralRelator (i : Bool) (j : Fin 7) :
    exponent i (centralRelator j : Central) = Multiplicative.ofAdd (exponentVector i j) := by
  change FreeGroup.lift _ (relator j) = _
  rw [relator, map_word]
  cases i <;> fin_cases j <;>
    simp [word, exponentVector, FreeGroup.lift_apply_of,
      ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_neg]

theorem exponent_collect_false (n : Fin 7 → ℤ) :
    (exponent false (collect n : Central)).toAdd =
      2 * n 0 + 8 * n 2 + 14 * n 3 + 26 * n 4 + 27 * n 5 + 32 * n 6 := by
  simp [collect, exponent_centralRelator, exponentVector, mul_comm]

theorem exponent_collect_true (n : Fin 7 → ℤ) :
    (exponent true (collect n : Central)).toAdd =
      3 * n 1 - 14 * n 3 - 6 * n 4 + 9 * n 5 + 8 * n 6 := by
  simp [collect, exponent_centralRelator, exponentVector, mul_comm, sub_eq_add_neg]
  ring

theorem kernel_derived_normal_form {x : Central} (hxD : x ∈ commutator Central)
    (hx : centralProjection x = 1) :
    ∃ n : Fin 7 → ℤ, x = (collect n : Central) ∧
      2 * n 0 + 8 * n 2 + 14 * n 3 + 26 * n 4 + 27 * n 5 + 32 * n 6 = 0 ∧
      3 * n 1 - 14 * n 3 - 6 * n 4 + 9 * n 5 + 8 * n 6 = 0 := by
  obtain ⟨n, rfl⟩ := kernel_normal_form hx
  refine ⟨n, rfl, ?_, ?_⟩
  · have h := Abelianization.commutator_subset_ker (exponent false) hxD
    change exponent false (collect n : Central) = 1 at h
    simpa only [exponent_collect_false, toAdd_one] using congrArg Multiplicative.toAdd h
  · have h := Abelianization.commutator_subset_ker (exponent true) hxD
    change exponent true (collect n : Central) = 1 at h
    simpa only [exponent_collect_true, toAdd_one] using congrArg Multiplicative.toAdd h

/-- The square of the marked lift after correcting its exponent sums. -/
def markedSquare : Subgroup.center Central :=
  centralRelator 0 ^ (27 : ℤ) * centralRelator 1 ^ (6 : ℤ) * centralRelator 5 ^ (-2 : ℤ)

/-- The zero-exponent cycle in the fourth power of the first commutator. -/
def commutatorCycle : Subgroup.center Central :=
  centralRelator 2 * centralRelator 0 ^ (-4 : ℤ)

/-- The second potentially independent multiplier generator. -/
def secondCycle : Subgroup.center Central :=
  centralRelator 3 ^ (3 : ℤ) * centralRelator 0 ^ (-21 : ℤ) *
    centralRelator 1 ^ (14 : ℤ)

def fourthCycle : Subgroup.center Central :=
  centralRelator 4 * centralRelator 0 ^ (-13 : ℤ) * centralRelator 1 ^ (2 : ℤ)

def lastCycle : Subgroup.center Central :=
  centralRelator 3 * centralRelator 6 * centralRelator 0 ^ (-23 : ℤ) *
    centralRelator 1 ^ (2 : ℤ)

theorem exponent_lattice (n : Fin 7 → ℤ)
    (ha : 2 * n 0 + 8 * n 2 + 14 * n 3 + 26 * n 4 + 27 * n 5 + 32 * n 6 = 0)
    (hb : 3 * n 1 - 14 * n 3 - 6 * n 4 + 9 * n 5 + 8 * n 6 = 0) :
    ∃ m t : ℤ, n 5 = 2 * m ∧ n 3 = 3 * t + n 6 ∧
      n 0 = -4 * n 2 - 21 * t - 13 * n 4 - 27 * m - 23 * n 6 ∧
      n 1 = 14 * t + 2 * n 4 - 6 * m + 2 * n 6 := by
  refine ⟨n 5 / 2, (n 3 - n 6) / 3, ?_, ?_, ?_, ?_⟩ <;> omega

theorem collect_zero_exponent (n : Fin 7 → ℤ)
    (ha : 2 * n 0 + 8 * n 2 + 14 * n 3 + 26 * n 4 + 27 * n 5 + 32 * n 6 = 0)
    (hb : 3 * n 1 - 14 * n 3 - 6 * n 4 + 9 * n 5 + 8 * n 6 = 0) :
    ∃ m t : ℤ, collect n = markedSquare ^ (-m) * commutatorCycle ^ n 2 *
      secondCycle ^ t * fourthCycle ^ n 4 * lastCycle ^ n 6 := by
  obtain ⟨m, t, h5, h3, h0, h1⟩ := exponent_lattice n ha hb
  refine ⟨m, t, ?_⟩
  dsimp [collect, markedSquare, commutatorCycle, secondCycle, fourthCycle, lastCycle]
  rw [h0, h1, h3, h5]
  -- Additive normalization avoids expanding the concrete quotient during AC matching.
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module
def markedLift : Central := centralGenerator false *
  ((centralRelator 0 ^ (13 : ℤ) * centralRelator 1 ^ (3 : ℤ) *
    centralRelator 5 ^ (-1 : ℤ) : Subgroup.center Central) : Central)

theorem markedLift_projection : centralProjection markedLift = generator false := by
  simp [markedLift, centralRelator, centralGenerator, generator]
  rfl

theorem markedLift_sq : markedLift ^ 2 = (markedSquare : Central) := by
  let t : Subgroup.center Central :=
    centralRelator 0 ^ (13 : ℤ) * centralRelator 1 ^ (3 : ℤ) * centralRelator 5 ^ (-1 : ℤ)
  have hc : Commute (centralGenerator false) (t : Central) :=
    Subgroup.mem_center_iff.mp t.property _
  have he : centralGenerator false ^ 2 = (centralRelator 0 : Central) :=
    (centralRelator_val 0).symm
  change (centralGenerator false * (t : Central)) ^ 2 = _
  rw [hc.mul_pow, he]
  change ((centralRelator 0 * t ^ 2 : Subgroup.center Central) : Central) = _
  apply congrArg Subtype.val
  dsimp [t, markedSquare]
  simp only [zpow_neg, mul_pow, inv_pow]
  change centralRelator 0 * (centralRelator 0 ^ 26 * centralRelator 1 ^ 6 *
    (centralRelator 5 ^ 2)⁻¹) = centralRelator 0 ^ 27 * centralRelator 1 ^ 6 *
    (centralRelator 5 ^ 2)⁻¹
  rw [← mul_assoc, ← mul_assoc, ← pow_succ']

private def sourceCommutator {H : Type*} [Group H] (a b : H) := a⁻¹ * b⁻¹ * a * b

private theorem sourceCommutator_conj_inverse {H : Type*} [Group H] (a w : H)
    (ha : a ^ 2 ∈ Subgroup.center H) :
    MulAut.conj a⁻¹ (sourceCommutator a w) = (sourceCommutator a w)⁻¹ := by
  have hc : a ^ 2 * w⁻¹ = w⁻¹ * a ^ 2 :=
    (Subgroup.mem_center_iff.mp ha _).symm
  have hi : a ^ (-2 : ℤ) * w⁻¹ = w⁻¹ * a ^ (-2 : ℤ) := by
    simpa using (show Commute (a ^ 2) w⁻¹ from hc).inv_left.eq
  simp only [MulAut.conj_apply, inv_inv, sourceCommutator]
  calc
    _ = a ^ (-2 : ℤ) * w⁻¹ * a * w * a := by group
    _ = w⁻¹ * a ^ (-2 : ℤ) * a * w * a := by rw [hi]
    _ = _ := by group

private theorem central_sourceCommutator_power_sq {H : Type*} [Group H]
    (a w : H) (n : ℕ) (ha : a ^ 2 ∈ Subgroup.center H)
    (hc : sourceCommutator a w ^ n ∈ Subgroup.center H) :
    (sourceCommutator a w ^ n) ^ 2 = 1 := by
  have he : (sourceCommutator a w ^ n)⁻¹ = sourceCommutator a w ^ n := by
    calc
      _ = MulAut.conj a⁻¹ (sourceCommutator a w ^ n) := by
        rw [map_pow, sourceCommutator_conj_inverse a w ha, inv_pow]
      _ = _ := by simp [Subgroup.mem_center_iff.mp hc a⁻¹, mul_assoc]
  rw [pow_two]
  nth_rw 1 [← he]
  exact inv_mul_cancel _

private theorem commutatorCycle_val : (commutatorCycle : Central) =
    sourceCommutator (centralGenerator false) (centralGenerator true) ^ 4 := by
  let a := centralGenerator false
  let b := centralGenerator true
  have ha : a ^ 2 ∈ Subgroup.center Central := (centralRelator 0).property
  have hc : Commute (a ^ 2) (sourceCommutator a b) :=
    (Subgroup.mem_center_iff.mp ha _).symm
  have he : a * b⁻¹ * a * b = a ^ 2 * sourceCommutator a b := by
    dsimp [sourceCommutator]
    group
  change (a * b⁻¹ * a * b) ^ 4 * (a ^ 2) ^ (-4 : ℤ) = _
  rw [he, hc.mul_pow]
  have hc' := hc.pow_pow 4 4
  rw [hc'.eq]
  group
  rfl

theorem commutatorCycle_sq : commutatorCycle ^ 2 = 1 := by
  apply Subtype.ext
  change (commutatorCycle : Central) ^ 2 = 1
  rw [commutatorCycle_val]
  exact central_sourceCommutator_power_sq _ _ 4 (centralRelator 0).property
    (commutatorCycle_val ▸ commutatorCycle.property)

/-- The remaining finite central collection problem. This record has no witness
until the independent central-identities calculation has been proved. -/
structure CollectionIdentities : Prop where
  commutator_eq : commutatorCycle = markedSquare
  fourth_eq : fourthCycle = markedSquare
  last_eq : lastCycle = markedSquare * secondCycle
  second_sq : secondCycle ^ 2 = 1

theorem markedSquare_sq (h : CollectionIdentities) : markedSquare ^ 2 = 1 := by
  rw [← h.commutator_eq]
  exact commutatorCycle_sq

/-- The five integral cycles reduce to the two specified kernel generators. -/
theorem derived_kernel_two_generator_form (h : CollectionIdentities)
    {x : Central} (hxD : x ∈ commutator Central) (hx : centralProjection x = 1) :
    ∃ u v : ℤ, x = ((markedSquare ^ u * secondCycle ^ v : Subgroup.center Central) : Central) := by
  obtain ⟨n, rfl, ha, hb⟩ := kernel_derived_normal_form hxD hx
  obtain ⟨m, t, he⟩ := collect_zero_exponent n ha hb
  refine ⟨-m + n 2 + n 4 + n 6, t + n 6, ?_⟩
  apply congrArg Subtype.val
  rw [he, h.commutator_eq, h.fourth_eq, h.last_eq]
  -- Additive normalization avoids expanding the concrete quotient during AC matching.
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem derived_kernel_four_cases (h : CollectionIdentities)
    {x : Central} (hxD : x ∈ commutator Central) (hx : centralProjection x = 1) :
    x = 1 ∨ x = (markedSquare : Central) ∨ x = (secondCycle : Central) ∨
      x = (markedSquare : Central) * (secondCycle : Central) := by
  obtain ⟨u, v, rfl⟩ := derived_kernel_two_generator_form h hxD hx
  rw [zpow_eq_zpow_emod u (show markedSquare ^ (2 : ℤ) = 1 from markedSquare_sq h),
    zpow_eq_zpow_emod v (show secondCycle ^ (2 : ℤ) = 1 from h.second_sq)]
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  have hv : v % 2 = 0 ∨ v % 2 = 1 := by omega
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp [hu, hv]

@[simp] theorem centralProjection_centralRelator (i : Fin 7) :
    centralProjection (centralRelator i : Central) = 1 := toPresented_relator i

@[simp] theorem secondCycle_projection : centralProjection (secondCycle : Central) = 1 := by
  simp [secondCycle]

end CentralKernel
end Rudvalis.Multiplier.TwoPrimary.LocalPresentation
