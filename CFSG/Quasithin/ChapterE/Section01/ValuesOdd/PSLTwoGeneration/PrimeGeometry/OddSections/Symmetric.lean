module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.Common
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
# The S₄ local E1 calculation

Use the action on the three double transpositions to identify the quotient
by O₂(S₄) with S₃. A nonnormal four-group cannot lie in the kernel: equal
orders would make it the normal kernel. Its nontrivial two-group image has
order two and acts nontrivially on the normal cubic subgroup of S₃.
The first isomorphism theorem transports every clause to the literal
intrinsic quotient of the supplied group model.

Source: Aschbacher–Smith, E.1.2(E1) and E.1.5, printed p.210.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections

private theorem alternating_three_selfCentralizing :
    centralizer (alternatingGroup (Fin 3) : Set (Equiv.Perm (Fin 3))) ≤
      alternatingGroup (Fin 3) := by
  intro x hx
  have hc := mem_centralizer_iff.mp hx
  exact (show ∀ x : Equiv.Perm (Fin 3),
    (∀ y : Equiv.Perm (Fin 3), y ∈ alternatingGroup (Fin 3) → y * x = x * y) →
      x ∈ alternatingGroup (Fin 3) by
        simp only [Equiv.Perm.mem_alternatingGroup]
        decide +kernel) x hc

/-- A nonnormal elementary four-group in an actual S₄ model gives E1 at 3. -/
theorem symmetric_intrinsic {X : Type*} [Group X] [Finite X]
    (B : Subgroup X) [IsElementaryAbelian 2 B] (hB : Nat.card B = 4)
    (hn : ¬ B.Normal) (e : X ≃* Equiv.Perm (Fin 4)) :
    let Q := X ⧸ pCore 2 X
    let a := B.map (QuotientGroup.mk' (pCore 2 X))
    IsPGroup 2 (Q ⧸ pCore 3 Q) ∧ pCore 3 Q ≠ ⊥ ∧
      pCore 3 Q = ⁅pCore 3 Q, a⁆ ∧ Group.rank a = 1 := by
  let f : X →* Equiv.Perm (Fin 3) :=
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom.comp e.toMonoidHom
  have hf : Function.Surjective f :=
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective.comp e.surjective
  have h3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h4 : Nat.card X = 24 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hkcard : Nat.card f.ker = 4 := by
    have hh := f.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      h3, h4] at hh
    omega
  have hk : f.ker = pCore 2 X := ker_eq_twoCore_of_surjective_perm_three f hf
    (IsPGroup.of_card (n := 2) (by simpa using hkcard))
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hne : B.map f ≠ ⊥ := by
    intro hh
    have hle : B ≤ f.ker := (map_eq_bot_iff B).mp hh
    have heq : B = f.ker := eq_of_le_of_card_ge hle (by rw [hkcard, hB])
    exact hn (by rw [heq]; infer_instance)
  apply intrinsic_of_epimorphism B f hf hk
  apply primeSection Nat.prime_three (by decide) (alternatingGroup (Fin 3))
    (by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
    h3 alternating_three_selfCentralizing (B.map f) hne

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
