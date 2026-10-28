module

public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.Index

/-!
# The two elementary four-groups in a semidihedral group of order sixteen

The sixteen-element standard model has just two elementary four-subgroups.
A certificate checks the pairs of distinct commuting involutions; an actual
isomorphism from a four-group supplies such a pair. Transport gives the
same two-subgroup bound for every SD16 carrier. This is the local counting
input for the PSL₃(3) automorphism containment in Aschbacher--Smith 2.5.8(5),
printed p.556.
-/

public section
open Subgroup
namespace Semidihedral
private abbrev C8 := Multiplicative (ZMod 8)
private abbrev C2 := Multiplicative (ZMod 2)
private def twist : MulAut C8 where
  toFun x := .ofAdd (3 * x.toAdd)
  invFun x := .ofAdd (3 * x.toAdd)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel
private def action : C2 →* MulAut C8 where
  toFun i := twist ^ i.toAdd.val
  map_one' := rfl
  map_mul' := by intro i j; ext x; revert i j x; decide +kernel
private abbrev D := C8 ⋊[action] C2
private abbrev V := Multiplicative (ZMod 2 × ZMod 2)
private abbrev r : D := SemidirectProduct.inl (.ofAdd 1)
private abbrev s : D := SemidirectProduct.inr (.ofAdd 1)
private instance : Fintype D := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
private theorem d_equiv : Nonempty (D ≃* StandardModel 4 (by omega)) := by
  apply standardModel_equiv_of_presentation (by omega : 4 ≤ 4) r s
  · rw [orderOf_injective _ SemidirectProduct.inl_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
    norm_num
  · rw [orderOf_injective _ SemidirectProduct.inr_injective, orderOf_ofAdd_eq_addOrderOf,
      ZMod.addOrderOf_one]
  · decide +kernel
  · apply top_le_iff.mp
    intro x _
    have hc : ∀ x : D, ∃ i j : Fin 8, x = r ^ i.val * s ^ j.val := by decide +kernel
    obtain ⟨i, j, rfl⟩ := hc x
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (subset_closure (by simp)) _)
  · rw [SemidirectProduct.card]; simp

private def fourZero : Subgroup D where
  carrier := {x | x = 1 ∨ x = r ^ 4 ∨ x = s ∨ x = r ^ 4 * s}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
  inv_mem' := by decide +kernel

private def fourOne : Subgroup D where
  carrier := {x | x = 1 ∨ x = r ^ 4 ∨ x = r ^ 2 * s ∨ x = r ^ 6 * s}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
  inv_mem' := by decide +kernel

private instance : DecidablePred (· ∈ fourZero) := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
private instance : DecidablePred (· ∈ fourOne) := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private theorem fourZero_card : Nat.card fourZero = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private theorem fourOne_card : Nat.card fourOne = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel

private theorem pair_coverage : ∀ a b : D, a ≠ 1 → b ≠ 1 → a ≠ b →
    a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
    (a ∈ fourZero ∧ b ∈ fourZero) ∨ (a ∈ fourOne ∧ b ∈ fourOne) := by
  decide +kernel

/-- The fixed standard model contains at most two elementary four-subgroups. -/
private theorem d_four_cover : ∃ F₀ F₁ : Subgroup D,
    ∀ E : Subgroup D, IsKleinFour E → E = F₀ ∨ E = F₁ := by
  refine ⟨fourZero, fourOne, ?_⟩
  intro E hE
  let := hE
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := V) (G₂ := E)
  let f := E.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := E.subtype_injective.comp e.injective
  let x : V := .ofAdd (1, 0)
  let y : V := .ofAdd (0, 1)
  have hx : f x ≠ 1 := fun h => (by decide : x ≠ 1) (hf (h.trans f.map_one.symm))
  have hy : f y ≠ 1 := fun h => (by decide : y ≠ 1) (hf (h.trans f.map_one.symm))
  have hxy : f x ≠ f y := fun h => (by decide : x ≠ y) (hf h)
  have hx2 : (f x) ^ 2 = 1 := by rw [← map_pow]; exact (congrArg f (by decide : x ^ 2 = 1)).trans f.map_one
  have hy2 : (f y) ^ 2 = 1 := by rw [← map_pow]; exact (congrArg f (by decide : y ^ 2 = 1)).trans f.map_one
  have hcomm : f x * f y = f y * f x := by
    simpa only [map_mul] using congrArg f (show x * y = y * x by decide)
  have hle (F : Subgroup D) (hxF : f x ∈ F) (hyF : f y ∈ F) : E ≤ F := by
    intro z hz
    obtain ⟨v, hv⟩ := e.surjective ⟨z, hz⟩
    have hvz : f v = z := congrArg Subtype.val hv
    rw [← hvz]
    have hc : ∀ v : V, v = 1 ∨ v = x ∨ v = y ∨ v = x * y := by decide +kernel
    rcases hc v with rfl | rfl | rfl | rfl
    · rw [map_one]; exact F.one_mem
    · exact hxF
    · exact hyF
    · rw [map_mul]; exact F.mul_mem hxF hyF
  rcases pair_coverage (f x) (f y) hx hy hxy hx2 hy2 hcomm with h | h
  · exact Or.inl (eq_of_le_of_card_ge (hle fourZero h.1 h.2) (by rw [fourZero_card, IsKleinFour.card_four]))
  · exact Or.inr (eq_of_le_of_card_ge (hle fourOne h.1 h.2) (by rw [fourOne_card, IsKleinFour.card_four]))

/-- The two-four bound is intrinsic to every SD16 carrier. -/
theorem sixteen_four_cover {K : Type*} [Group K]
    (e : K ≃* StandardModel 4 (by omega)) :
    ∃ F₀ F₁ : Subgroup K, ∀ E : Subgroup K, IsKleinFour E → E = F₀ ∨ E = F₁ := by
  obtain ⟨d⟩ := d_equiv
  let e := e.trans d.symm
  obtain ⟨F₀, F₁, hF⟩ := d_four_cover
  refine ⟨F₀.map e.symm.toMonoidHom, F₁.map e.symm.toMonoidHom, ?_⟩
  intro E hE
  let := hE
  let eE := E.equivMapOfInjective e.toMonoidHom e.injective
  have hc : IsKleinFour (E.map e.toMonoidHom) := {
    card_four := (Nat.card_congr eE.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).symm.trans IsKleinFour.exponent_two }
  have hm : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [map_map]; simp
  rcases hF (E.map e.toMonoidHom) hc with h | h
  · exact Or.inl (hm.symm.trans (congrArg (Subgroup.map e.symm.toMonoidHom) h))
  · exact Or.inr (hm.symm.trans (congrArg (Subgroup.map e.symm.toMonoidHom) h))

end Semidihedral
