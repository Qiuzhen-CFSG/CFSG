module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Tree
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The finite-cycle step of the real-valency argument

A cyclic ordering reversed by an involution that fixes every incident label
has length at most two: its successor equals its inverse. The interface below
keeps the actual dual representations and identifies real lifted characters
with fixed labels.

This is a conditional reduction of Feit VII.2.24 (proof p.303). No existence
of this data is asserted. Constructing the ordering from serial vertex
modules (VII.2.20, VII.2.23), proving duality reverses their socle series, and
identifying real irreducibles with self-dual modules remain mathematical
obligations of the source assembly.
-/

public section
open scoped Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine
namespace RealValency

/-- The cyclic ordering and actual duality action at one ordinary vertex.
This output interface has no existence instance and no valency field. -/
structure LocalDualityOrder {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {I : Type*} [Fintype I] {χ : I → ConjClassFunction G} {block : Finset I}
    {p m n : ℕ} {L : CyclicRootLift K m} (t : Tree χ block p n L)
    (v : {i // i ∈ block}) where
  successor : Equiv.Perm ↥(t.incident v)
  cyclic : successor.IsCycleOn Set.univ
  conjugate : Equiv.Perm ↥(t.incident v)
  dual_equiv : ∀ e, Nonempty ((t.rep e.val).dual.Equiv (t.rep (conjugate e).val))
  fixed_iff_real : ∀ e, conjugate e = e ↔ ∀ g, ¬p ∣ orderOf g →
    star (L.value (t.rep e.val) g) = L.value (t.rep e.val) g
  reverses : conjugate * successor * conjugate⁻¹ = successor⁻¹

private theorem card_le_two_of_reversing_cycle {A : Type*} [Fintype A]
    (s c : Equiv.Perm A) (hcycle : s.IsCycleOn Set.univ)
    (hfix : ∀ a, c a = a) (hrev : c * s * c⁻¹ = s⁻¹) :
    Fintype.card A ≤ 2 := by
  classical
  have hc : c = 1 := by
    ext a
    exact hfix a
  have hs : s = s⁻¹ := by simpa [hc] using hrev
  have hs2 : s ^ 2 = 1 := by
    rw [pow_two, ← mul_inv_cancel s]
    exact congrArg (s * ·) hs
  rcases isEmpty_or_nonempty A with h | h
  · let : IsEmpty A := h
    simp
  · let : Nonempty A := h
    let a : A := Classical.arbitrary A
    have hcycle' : s.IsCycleOn (↑(Finset.univ : Finset A)) := by simpa using hcycle
    have hdvd := (hcycle'.pow_apply_eq (Finset.mem_univ a)).mp
      (show (s ^ 2) a = a by rw [hs2]; rfl)
    exact Nat.le_of_dvd (by decide) (by simpa using hdvd)

namespace LocalDualityOrder

variable {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {I : Type*} [Fintype I] {χ : I → ConjClassFunction G} {block : Finset I}
    {p m n : ℕ} {L : CyclicRootLift K m} {t : Tree χ block p n L}
    {v : {i // i ∈ block}}

/-- Conditional finite-cycle deduction; constructing the duality order is
a separate module-theoretic obligation. -/
theorem incident_card_le_two (o : LocalDualityOrder t v)
    (hreal : ∀ e : ↥(t.incident v), ∀ g, ¬p ∣ orderOf g →
      star (L.value (t.rep e.val) g) = L.value (t.rep e.val) g) :
    (t.incident v).card ≤ 2 := by
  simpa only [Fintype.card_coe] using card_le_two_of_reversing_cycle o.successor o.conjugate o.cyclic
    (fun e => (o.fixed_iff_real e).mpr (hreal e)) o.reverses

end LocalDualityOrder
end RealValency
end Representation.CyclicDefect.PrimeOrderRealLine
