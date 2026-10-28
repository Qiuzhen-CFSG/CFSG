module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Presentation
public import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.Group

/-!
# Central relator products and their exponent sums

In the literal free central extension F/[F,R], the kernel over F/R is the
image of the integer powers of the seven central relators. This follows
from normal-closure generation: that image is central, hence normal.
The two exponent homomorphisms vanish on the derived subgroup and give
the exact two integral constraints on those seven powers.

The last three relators have square one. Indeed, when a² is central,
conjugation by a⁻¹ inverts [a,w]; any central power of [a,w] is therefore
its own inverse. This proves that the specified defect has square one,
without assuming that it generates the derived kernel.

`powerCycle` and `mixedCycle` are the two zero-exponent vectors involving
the first four relators. Their images and the last three central relators
are the remaining collection problem; no equality between them is assumed.

Source: Wilson, Nickerson and Bray, ATLAS `S62G1-P1.M`, with the literal
commutator convention and attribution recorded in `Presentation.lean`.
Aschbacher–Smith I.1.1, printed p.407, fixes the covering convention.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
namespace CentralCollection
open scoped IsMulCommutative

def centralRelator (i : Fin 7) : Subgroup.center Central :=
  ⟨toCentral (relator i), centralProjection_ker_le_center (by
    change toPresented (relator i) = 1
    exact toPresented_relator i)⟩

theorem centralRelator_val (i : Fin 7) :
    (centralRelator i : Central) = word (centralGenerator false) (centralGenerator true) i :=
  map_word toCentral _ _ i

theorem centralRelator_six : (centralRelator 6 : Central) = defect := rfl

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
  if i then ![0, 7, 9, 24, 0, 0, 0] else ![2, 0, 9, 12, 0, 0, 0]

theorem exponent_centralRelator (i : Bool) (j : Fin 7) :
    exponent i (centralRelator j : Central) = Multiplicative.ofAdd (exponentVector i j) := by
  change FreeGroup.lift _ (relator j) = _
  rw [relator, map_word]
  cases i <;> fin_cases j <;>
    simp [word, sourceCommutator, exponentVector, FreeGroup.lift_apply_of,
      ← ofAdd_nsmul, ← ofAdd_add,
      ← ofAdd_neg]

theorem exponent_collect_false (n : Fin 7 → ℤ) :
    (exponent false (collect n : Central)).toAdd = 2 * n 0 + 9 * n 2 + 12 * n 3 := by
  simp [collect, exponent_centralRelator, exponentVector, mul_comm]

theorem exponent_collect_true (n : Fin 7 → ℤ) :
    (exponent true (collect n : Central)).toAdd = 7 * n 1 + 9 * n 2 + 24 * n 3 := by
  simp [collect, exponent_centralRelator, exponentVector, mul_comm]

theorem kernel_derived_normal_form {x : Central} (hxD : x ∈ commutator Central)
    (hx : centralProjection x = 1) :
    ∃ n : Fin 7 → ℤ, x = (collect n : Central) ∧
      2 * n 0 + 9 * n 2 + 12 * n 3 = 0 ∧
      7 * n 1 + 9 * n 2 + 24 * n 3 = 0 := by
  obtain ⟨n, rfl⟩ := kernel_normal_form hx
  refine ⟨n, rfl, ?_, ?_⟩
  · have h := Abelianization.commutator_subset_ker (exponent false) hxD
    change exponent false (collect n : Central) = 1 at h
    simpa only [exponent_collect_false, toAdd_one] using
      congrArg Multiplicative.toAdd h
  · have h := Abelianization.commutator_subset_ker (exponent true) hxD
    change exponent true (collect n : Central) = 1 at h
    simpa only [exponent_collect_true, toAdd_one] using
      congrArg Multiplicative.toAdd h

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

private theorem centralGenerator_sq_central :
    centralGenerator false ^ 2 ∈ Subgroup.center Central := by
  simpa only [centralRelator_val, word, Matrix.cons_val_zero] using
    (centralRelator 0).property

theorem centralRelator_four_sq : centralRelator 4 ^ 2 = 1 := by
  apply Subtype.ext
  have hc := (centralRelator 4).property
  simp only [centralRelator_val, word] at hc ⊢
  exact central_sourceCommutator_power_sq _ _ _ centralGenerator_sq_central hc

theorem centralRelator_five_sq : centralRelator 5 ^ 2 = 1 := by
  apply Subtype.ext
  have hc := (centralRelator 5).property
  simp only [centralRelator_val, word] at hc ⊢
  exact central_sourceCommutator_power_sq _ _ _ centralGenerator_sq_central hc

theorem centralRelator_six_sq : centralRelator 6 ^ 2 = 1 := by
  apply Subtype.ext
  have hc := (centralRelator 6).property
  simp only [centralRelator_val, word] at hc ⊢
  exact central_sourceCommutator_power_sq _ _ _ centralGenerator_sq_central hc

theorem defect_sq : defect ^ 2 = 1 :=
  congrArg Subtype.val centralRelator_six_sq

def powerCycle : Fin 7 → ℤ := ![-63, -18, 14, 0, 0, 0, 0]
def mixedCycle : Fin 7 → ℤ := ![-15, -6, 2, 1, 0, 0, 0]

def powerDefect : Subgroup.center Central := collect powerCycle
def mixedDefect : Subgroup.center Central := collect mixedCycle


end CentralCollection
end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
