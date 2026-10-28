module

public import Theory.GroupTheory.SmallFittingResidual
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two-perfect actors on a quotient of order three

A two-perfect subgroup normalizing A acts trivially on A/O₂(A) when that
quotient has order three: its automorphism group is a two-group. Thus the
actual commutator lies in the embedded two-core of A.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
sentence of the proof of 15.4.23, printed p.1165.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Two-perfect actors centralize a normalized cyclic quotient of order three.
Only the automorphism group of this actual quotient is used. -/
theorem commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three
    (A B : Subgroup G) (hB : IsPPerfect 2 B)
    (hBA : B ≤ normalizer (A : Set G))
    (hA : Nat.card (A ⧸ pCore 2 A) = 3) : ⁅B, A⁆ ≤ A.pCoreIn 2 := by
  let α : B →* MulAut A := A.normalizerMonoidHom.comp (inclusion hBA)
  let f : B →* MulAut (A ⧸ pCore 2 A) := (quotientAut (pCore 2 A)).comp α
  have hf : f = 1 := hB.hom_eq_one_of_isPGroup
    (aut_two_of_card_one_or_three (A ⧸ pCore 2 A) (Or.inr hA)) f
  apply commutator_le.mpr
  intro b hb a ha
  let b' : B := ⟨b, hb⟩
  let a' : A := ⟨a, ha⟩
  have he : QuotientGroup.mk' (pCore 2 A) (α b' a') =
      QuotientGroup.mk' (pCore 2 A) a' := by
    have hfix := congrArg (fun t : B →* MulAut (A ⧸ pCore 2 A) =>
      t b' (QuotientGroup.mk' (pCore 2 A) a')) hf
    simpa only [f, MonoidHom.comp_apply, quotientAut_apply_mk,
      MonoidHom.one_apply, MulAut.one_apply] using hfix
  have hc : α b' a' / a' ∈ pCore 2 A := QuotientGroup.eq_iff_div_mem.mp he
  change _ ∈ (pCore 2 A).map A.subtype
  refine ⟨α b' a' / a', hc, ?_⟩
  change (b * a * b⁻¹) / a = ⁅b, a⁆
  simp only [div_eq_mul_inv, commutatorElement_def]

end Subgroup
