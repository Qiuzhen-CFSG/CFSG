module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index

/-!
# Centralizers from fixed points and stabilizer intersections

Count the elements carrying a chosen point into the fixed points of an actor.
Orbit–stabilizer makes this the stabilizer order times the number of fixed
points in the orbit. Inverting the transporter and counting its conjugation
fiber instead gives the actor's centralizer order times the intersection of
its conjugacy class with the point stabilizer. This proves the usual
fixed-point ratio formula without assuming that the action is faithful.
-/

open Subgroup
noncomputable section
namespace MulAction
variable {G X : Type*} [Group G] [MulAction G X]

private def orbitPreimageEquiv (a : X) (P : X → Prop) :
    {g : G // P (g • a)} ≃ {b : orbit G a // P b.val} × stabilizer G a := by
  classical
  let s (b : orbit G a) : G := b.property.choose
  have hs (b : orbit G a) : s b • a = b.val := b.property.choose_spec
  refine {
    toFun := fun g => ⟨⟨⟨g.val • a, mem_orbit_iff.mpr ⟨g.val, rfl⟩⟩, g.property⟩,
      ⟨(s ⟨g.val • a, mem_orbit_iff.mpr ⟨g.val, rfl⟩⟩)⁻¹ * g.val, ?_⟩⟩
    invFun := fun p => ⟨s p.1.val * p.2.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [mem_stabilizer_iff, mul_smul]
    have he : s ⟨g.val • a, mem_orbit_iff.mpr ⟨g.val, rfl⟩⟩ • a = g.val • a := hs _
    exact (congrArg (fun y => (s ⟨g.val • a, mem_orbit_iff.mpr ⟨g.val, rfl⟩⟩)⁻¹ • y)
      he.symm).trans (inv_smul_smul _ _)
  · simpa only [mul_smul, (mem_stabilizer_iff.mp p.2.property), hs] using p.1.property
  · intro g
    apply Subtype.ext
    exact mul_inv_cancel_left _ _
  · rintro ⟨b, h⟩
    have he : (s b.val * h.val) • a = b.val.val := by
      rw [mul_smul, mem_stabilizer_iff.mp h.property, hs]
    apply Prod.ext
    · exact Subtype.ext (Subtype.ext he)
    · apply Subtype.ext
      change (s ⟨(s b.val * h.val) • a, _⟩)⁻¹ * (s b.val * h.val) = h.val
      have hb : (⟨(s b.val * h.val) • a,
          mem_orbit_iff.mpr ⟨s b.val * h.val, rfl⟩⟩ : orbit G a) = b.val := Subtype.ext he
      rw [hb, inv_mul_cancel_left]

private theorem card_orbit_preimage (a : X) (P : X → Prop) :
    Nat.card {g : G // P (g • a)} =
      Nat.card {b : orbit G a // P b.val} * Nat.card (stabilizer G a) := by
  rw [Nat.card_congr (orbitPreimageEquiv a P), Nat.card_prod]
end MulAction

namespace MulAction
variable {G X : Type*} [Group G] [MulAction G X]

/-- Count transporters by conjugation and by their image of the base point. -/
public theorem centralizer_card_mul_conj_stabilizer (a : X) (x : G) :
    Nat.card (centralizer ({x} : Set G)) *
        Nat.card {h : stabilizer G a // IsConj (h : G) x} =
      Nat.card (stabilizer G a) *
        Nat.card {b : orbit G a // x • b.val = b.val} := by
  classical
  have h1 := card_orbit_preimage (G := G) a (fun b => x • b = b)
  have h2 := card_orbit_preimage (G := ConjAct G) x
    (fun y => y ∈ stabilizer G a)
  have hc : Nat.card (stabilizer (ConjAct G) x) =
      Nat.card (centralizer ({x} : Set G)) := by
    apply Nat.card_congr
    exact ((ConjAct.toConjAct (G := G)).toEquiv.subtypeEquiv (fun g => by
      rw [mem_centralizer_singleton_iff, mem_stabilizer_iff, ConjAct.smul_def,
        mul_inv_eq_iff_eq_mul]
      rfl)).symm
  have hi : Nat.card {b : orbit (ConjAct G) x // b.val ∈ stabilizer G a} =
      Nat.card {h : stabilizer G a // IsConj (h : G) x} := by
    apply Nat.card_congr
    exact {
      toFun := fun b => ⟨⟨b.val.val, b.property⟩, ConjAct.mem_orbit_conjAct.mp b.val.property⟩
      invFun := fun h => ⟨⟨h.val.val, ConjAct.mem_orbit_conjAct.mpr h.property⟩, h.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have ht : Nat.card {g : ConjAct G // (g • x) ∈ stabilizer G a} =
      Nat.card {g : G // x • (g • a) = g • a} := by
    apply Nat.card_congr
    let e : ConjAct G ≃ G := ConjAct.ofConjAct.toEquiv.trans (Equiv.inv G)
    apply e.subtypeEquiv
    intro g
    change (g • x) • a = a ↔ x • ((ConjAct.ofConjAct g)⁻¹ • a) =
      (ConjAct.ofConjAct g)⁻¹ • a
    rw [ConjAct.smul_def, mul_smul, mul_smul, eq_inv_smul_iff]
  rw [hc, hi, ht, h1] at h2
  exact (mul_comm _ _).trans (h2.symm.trans (mul_comm _ _))
end MulAction
