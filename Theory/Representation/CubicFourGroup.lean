module
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.Representation.BinaryOffender.CubicIrreducibleSection
public import Mathlib.Data.Fintype.Perm

/-!
# Cubic symmetry on an invariant four-group

An injected four-group on which a cubic operator has no fixed vector has
nontrivial cubic symmetry. Every commuting actor of exponent four fixes
that four-group, since its automorphism group is S₃.

Source application: Aschbacher–Smith 15.3.21, printed p.1127.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation
variable {D W E : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [Group E] [IsKleinFour E] [Nontrivial E]

/-- A cubic acting without fixed vectors on an invariant four-group forces a
commuting actor of exponent four to fix that four-group pointwise. -/
theorem cubic_fourgroup_fixed
    (ρ : Representation (ZMod 2) D W) (z t : D)
    (hz : z^3=1) (ht : t^4=1) (hzt : Commute z t)
    (a b : MulAut E) (j : E → W) (hj : Function.Injective j) (hj1 : j 1=0)
    (ha : ∀ x, j (a x)=ρ z (j x)) (hb : ∀ x, j (b x)=ρ t (j x))
    (hzero : ∀ v, ρ z v=v → v=0) : b=1 := by
  have hip (s : D) (c : MulAut E) (h : ∀ x, j (c x)=ρ s (j x))
      (n : ℕ) (x : E) : j ((c^n) x)=ρ (s^n) (j x) := by
    induction n with
    | zero => rw [pow_zero,pow_zero,map_one]; rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',map_mul]
      change j (c ((c^n) x))=ρ s (ρ (s^n) (j x))
      rw [h,ih]
  have ha3 : a^3=1 := by
    ext x
    apply hj
    rw [hip z a ha,hz,map_one]
    rfl
  have hane : a≠1 := by
    intro he
    have hall (x : E) : x=1 := by
      apply hj
      rw [hj1]
      apply hzero
      rw [←ha,he]
      rfl
    have : Subsingleton E := ⟨fun x y => (hall x).trans (hall y).symm⟩
    exact false_of_nontrivial_of_subsingleton E
  have hb4 : b^4=1 := by
    ext x
    apply hj
    rw [hip t b hb,ht,map_one]
    rfl
  have hab : a*b=b*a := by
    ext x
    apply hj
    change j (a (b x))=j (b (a x))
    rw [ha,hb,hb,ha]
    change (ρ z * ρ t) (j x)=(ρ t * ρ z) (j x)
    rw [←map_mul,←map_mul,hzt.eq]
  let e := IsKleinFour.autEquivPermThree E
  have hsmall : ∀ a b : Equiv.Perm (Fin 3), a^3=1 ∧ a≠1 ∧ b^4=1 ∧ a*b=b*a → b=1 := by
    decide +kernel
  apply e.injective
  rw [map_one]
  exact hsmall (e a) (e b) ⟨by rw [←map_pow,ha3,map_one],
    fun he => hane (e.injective (by simpa only [map_one] using he)),
    by rw [←map_pow,hb4,map_one],by rw [←map_mul,←map_mul,hab]⟩
end Representation
