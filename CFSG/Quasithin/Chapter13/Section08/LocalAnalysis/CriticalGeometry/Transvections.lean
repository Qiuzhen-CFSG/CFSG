module

public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.FixedCoatomDisplacement
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Transvections on the actual elementary abelian carrier

The line and hyperplane criteria below recognize genuine linear transvections
on `Additive W`, with its canonical binary vector-space structure. A common
commutator subgroup of order two gives a common center; a common fixed subgroup
of index two gives a common axis. The proofs construct the rank-one linear
formula, including its zero pairing condition.

These are the action-recognition steps needed in Aschbacher–Smith 13.8.9–10,
combined manuscript (1 March 2004), printed pp.949–950. Their application to
the source subgroups is in `CriticalGeometry.QuotientActions`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {W : Type*} [Group W] [IsElementaryAbelian 2 W]

/-- The canonical binary linear map of a group automorphism. -/
def binaryLinear (e : MulAut W) : Additive W ≃ₗ[ZMod 2] Additive W :=
  { e.toAdditive with map_smul' := ZMod.map_smul e.toAdditive }

/-- Displacement in an order-two subgroup gives a linear transvection. -/
theorem transvection_of_line (e : MulAut W) (Z : Subgroup W)
    (hcard : Nat.card Z = 2) (hd : ∀ w, w⁻¹ * e w ∈ Z) :
    binaryLinear e ∈ LinearEquiv.transvections (ZMod 2) (Additive W) := by
  obtain ⟨z, hz, hlast⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hcard
  have hz0 : Additive.ofMul (z : W) ≠ 0 := by
    intro h
    exact hz (Subtype.ext h)
  let v : Additive W := Additive.ofMul (z : W)
  let d : Additive W →ₗ[ZMod 2] Additive W :=
    (binaryLinear e).toLinearMap - LinearMap.id
  have hdline (x : Additive W) : d x ∈ Submodule.span (ZMod 2) {v} := by
    have hx := hd x.toMul
    by_cases hone : x.toMul⁻¹ * e x.toMul = 1
    · have he : d x = 0 := by
        change e x.toMul / x.toMul = 1
        simpa only [div_eq_mul_inv, mul_comm] using hone
      rw [he]
      exact Submodule.zero_mem _
    · have heq := congrArg Subtype.val
        (hlast ⟨x.toMul⁻¹ * e x.toMul, hx⟩ (fun h => hone (congrArg Subtype.val h)))
      have he : d x = v := by
        change e x.toMul / x.toMul = (z : W)
        simpa only [div_eq_mul_inv, mul_comm] using heq
      rw [he]
      exact Submodule.mem_span_singleton_self v
  let c := d.codRestrict (Submodule.span (ZMod 2) {v}) hdline
  let f : Additive W →ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.coord (ZMod 2) (Additive W) v hz0).toLinearMap.comp c
  have hfd (x : Additive W) : f x • v = binaryLinear e x - x :=
    LinearEquiv.coord_apply_smul (ZMod 2) (Additive W) v hz0 (c x)
  have hezmem : e (z : W) ∈ Z := by
    have := Z.mul_mem z.property (hd z)
    simpa only [mul_inv_cancel_left] using this
  have hezne : e (z : W) ≠ 1 := by
    intro h
    exact hz0 (e.injective (h.trans (map_one e).symm))
  have hez : e (z : W) = z := congrArg Subtype.val
    (hlast ⟨e z, hezmem⟩ (fun h => hezne (congrArg Subtype.val h)))
  have hf : f v = 0 := by
    have hh := hfd v
    have hh' : binaryLinear e v = v := hez
    rw [hh', sub_self] at hh
    exact (smul_eq_zero.mp hh).resolve_right hz0
  refine ⟨f, v, hf, ?_⟩
  ext x
  change binaryLinear e x = x + f x • v
  rw [hfd]
  abel

/-- Every actor has a transvection formula when its common displacement is a line. -/
theorem transvections_of_displacement_card_two (A : Subgroup (MulAut W))
    (hcard : Nat.card (commutatorAction A W) = 2) :
    ∀ a ∈ A, binaryLinear a ∈ LinearEquiv.transvections (ZMod 2) (Additive W) := by
  intro a ha
  apply transvection_of_line a (commutatorAction A W) hcard
  intro w
  exact subset_closure ⟨⟨a, ha⟩, w, mem_top w, rfl⟩

/-- A nontrivial subgroup of the actual automorphism group moves a vector. -/
theorem displacement_ne_bot (A : Subgroup (MulAut W)) (hA : A ≠ ⊥) :
    commutatorAction A W ≠ ⊥ := by
  intro h
  apply hA
  apply le_bot_iff.mp
  intro a ha
  apply mem_bot.mpr
  ext w
  have hd : w⁻¹ * a w ∈ commutatorAction A W :=
    subset_closure ⟨⟨a, ha⟩, w, mem_top w, rfl⟩
  rw [h, mem_bot] at hd
  exact (inv_mul_eq_one.mp hd).symm

/-- Every actor fixing a common hyperplane has a transvection formula. -/
theorem transvections_of_fixed_index_two [Finite W] (A : Subgroup (MulAut W))
    (hindex : (FixedPoints.subgroup A W).index = 2) :
    ∀ a ∈ A, binaryLinear a ∈ LinearEquiv.transvections (ZMod 2) (Additive W) := by
  intro a ha
  by_cases he : a = 1
  · subst a
    exact LinearEquiv.one_mem_transvections
  have hle : FixedPoints.subgroup A W ≤ FixedPoints.subgroup (zpowers a) W := by
    intro w hw b
    exact hw ⟨b, zpowers_le.mpr ha b.property⟩
  have hb := MulAut.commutatorAction_card_le_two_of_fixed_index_dvd_two a
    (hindex ▸ index_dvd_of_le hle)
  have hn : commutatorAction (zpowers a) W ≠ ⊥ :=
    displacement_ne_bot (zpowers a) (by simpa using he)
  have hc : Nat.card (commutatorAction (zpowers a) W) = 2 := by
    have hp := Nat.card_pos (α := commutatorAction (zpowers a) W)
    have hne : Nat.card (commutatorAction (zpowers a) W) ≠ 1 :=
      fun hh => hn (card_eq_one.mp hh)
    omega
  exact transvections_of_displacement_card_two (zpowers a) hc a (mem_zpowers a)
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
