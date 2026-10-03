module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# A Sylow-fixed generating involution in a group of order four

Let A act by automorphisms on a four-element group X. If a nonidentity
involution x is fixed by a supplied Sylow two-subgroup of A and its orbit
generates X, then that orbit contains every nonidentity element of X.
The action is exactly the instance supplied by the caller.

The stabilizer contains the Sylow subgroup, so its index, and hence the
orbit cardinality, is odd. Automorphisms fix identity, bounding the orbit
by the three nonidentity elements. A singleton orbit would generate only
the cyclic subgroup of x, of order at most two. Thus the orbit has size
three and exhausts the nonidentity elements.

This source-neutral finite-action lemma uses Mathlib's orbit-stabilizer
index formula, Sylow index theorem, and cyclic-subgroup cardinality formula.
The involution hypothesis is essential: a singleton orbit of a generator
can generate a cyclic group of order four.
-/

namespace MulAction

public theorem nonidentity_mem_orbit_of_card_four
    {A X : Type*} [Group A] [Finite A] [Group X] [Finite X]
    [act : MulDistribMulAction A X]
    (hcard : Nat.card X = 4) (x : X) (hx : x ≠ 1) (hx2 : x ^ 2 = 1)
    (S : Sylow 2 A) (hfix : ∀ s : S, (s : A) • x = x)
    (hgen : Subgroup.closure (orbit A x) = ⊤) :
    ∀ y : X, y ≠ 1 → y ∈ orbit A x := by
  classical
  have hS : (S : Subgroup A) ≤ stabilizer A x := by
    intro s hs
    exact hfix ⟨s, hs⟩
  have hodd : ¬ 2 ∣ (orbit A x).ncard := by
    rw [← index_stabilizer]
    intro hd
    exact S.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hS))
  have hsub : orbit A x ⊆ ({1} : Set X)ᶜ := by
    intro y hy
    obtain ⟨a, rfl⟩ := mem_orbit_iff.mp hy
    change a • x ≠ 1
    intro heq
    apply hx
    have heq' := congrArg (fun z : X => a⁻¹ • z) heq
    simpa only [inv_smul_smul, smul_one] using heq'
  have hc : (({1} : Set X)ᶜ).ncard = 3 := by
    rw [Set.ncard_compl, hcard, Set.ncard_singleton]
  have hle : (orbit A x).ncard ≤ 3 := by
    simpa only [hc] using Set.ncard_le_ncard hsub
  have hpos : 0 < (orbit A x).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨x, mem_orbit_self x⟩
  have hne : (orbit A x).ncard ≠ 1 := by
    intro hone
    obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hone
    have hxmem : x ∈ orbit A x := mem_orbit_self x
    have hxz : x = z := by simpa only [hz, Set.mem_singleton_iff] using hxmem
    subst z
    have hpowers : Subgroup.zpowers x = ⊤ := by
      rw [Subgroup.zpowers_eq_closure, ← hz]
      exact hgen
    have horder : orderOf x = 4 := by
      rw [← Nat.card_zpowers, hpowers, Subgroup.card_top, hcard]
    have hbound := orderOf_le_of_pow_eq_one (by decide : 0 < 2) hx2
    omega
  have hthree : (orbit A x).ncard = 3 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hodd
    omega
  have heq : orbit A x = ({1} : Set X)ᶜ :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hc, hthree])
  intro y hy
  rw [heq]
  exact hy

end MulAction
