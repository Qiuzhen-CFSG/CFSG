module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Models

/-!
# Actual higher-field carriers for the external-cubic reduction

The input retains all seven higher-field alternatives of 13.8.17: projective
linear two, special and projective linear or unitary three, and the actual
derived symplectic-four and G₂ groups. The signed special-three cases retain
the source congruence. Every constructor contains a genuine multiplicative
equivalence via the existing matrix-group predicates.

The proposed output list contains projective linear two, projective linear
three in odd degree, and projective unitary three in even degree. Unitary
predicates use a matrix field of order (2ⁿ)² = 2^(2*n), with conjugation
x ↦ x^(2ⁿ). These types specify the mathematical contract; this module does
not prove the rank restriction or the special/projective comparisons.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.17 and
proof of 13.8.20(a), printed pp.953–954 (PDF pp.970–971).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
open Chapter1.Section02.LocalModels Components.Models
universe u

/-- The full higher-field list, without torus automorphism or module premises. -/
inductive HigherFieldCarrier (D : Type u) [Group D] : Prop
  | linearTwo (n : ℕ) (hn : 1 < n) (iso : ClassicalGroup.IsPSL D 2 (2 ^ n))
  | projectiveThree (unitary : Bool) (n : ℕ) (hn : 1 < n)
      (iso : IsPSLSign D unitary 3 (2 ^ n))
  | specialThree (unitary : Bool) (n : ℕ) (hn : 1 < n)
      (hmod : (2 ^ n) % 3 = if unitary then 2 else 1)
      (iso : IsSLSign D unitary 3 (2 ^ n))
  | symplectic (n : ℕ) (hn : 1 < n) (iso : IsSp4DerivedAt D (2 ^ n))
  | g2 (n : ℕ) (hn : 1 < n) (iso : IsG2DerivedAt D (2 ^ n))

/-- The three genuine carriers remaining after the external cubic rank sieve. -/
inductive ExternalCarrier (D : Type u) [Group D] : Prop
  | linearTwo (n : ℕ) (hn : 1 < n) (iso : ClassicalGroup.IsPSL D 2 (2 ^ n))
  | linearThree (n : ℕ) (hn : 1 < n) (hodd : Odd n)
      (iso : ClassicalGroup.IsPSL D 3 (2 ^ n))
  | unitaryThree (n : ℕ) (hn : 1 < n) (heven : Even n)
      (iso : ClassicalGroup.IsPSU D 3 (2 ^ n))

/-- Forget only the higher-field restriction, retaining every actual model. -/
theorem HigherFieldCarrier.componentModel {D : Type u} [Group D]
    (h : HigherFieldCarrier D) : ComponentModel D := by
  cases h with
  | linearTwo n hn iso => exact .linear_two n hn iso
  | projectiveThree unitary n hn iso =>
      exact .projective_three unitary n (by cases unitary <;> simp [ThreeParameter] <;> omega) iso
  | specialThree unitary n hn hm iso =>
      exact .special_three unitary n (by cases unitary <;> simp [ThreeParameter] <;> omega) hm iso
  | symplectic n hn iso => exact .symplectic n (by omega) iso
  | g2 n hn iso => exact .g2 n (by omega) iso

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
end
