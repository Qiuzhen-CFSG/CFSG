module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.CentralInvolutions
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.GroupAction.ElementarySylowFixerBound

/-!
# Elementary pointwise Sylow fixers of M₂₄

The certified native Sylow subgroup has only two possible central elements.
Transport by Sylow conjugacy makes every Sylow center cyclic. The proved
innerness of every automorphism then bounds elementary groups of pointwise
Sylow fixers by two, as needed in Aschbacher–Smith, proof of 13.6.6, p.927.
All carrier and enumeration conventions come from the imported Witt model.
-/

public section
open Subgroup
namespace Sporadic.Mathieu
open M24LocalGeometry.SylowNormalizer

private theorem candidate_center_card_le_two : Nat.card (center candidate) ≤ 2 := by
  classical
  let f : center candidate → ({1, OrderEnumeration.element 106} : Finset candidate) :=
    fun z => ⟨z.val, by simpa only [Finset.mem_insert, Finset.mem_singleton] using
      central_element_cases z.val z.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ({1, OrderEnumeration.element 106} : Finset candidate) => z.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact Finset.card_le_two)

theorem m24_sylow_center_card_le_two (S : Sylow 2 M24) : Nat.card (center S) ≤ 2 := by
  let P : Sylow 2 M24 := Sylow.ofCard candidate (by
    rw [candidate_card, m24_order]
    decide +kernel)
  rw [Nat.card_congr (centerCongr (S.equiv P)).toEquiv]
  exact candidate_center_card_le_two

theorem m24_sylow_center_isCyclic (S : Sylow 2 M24) : IsCyclic (center S) :=
by
  apply isCyclic_of_card_dvd_prime (p := 2)
  have h := m24_sylow_center_card_le_two S
  have hp := Nat.card_pos (α := center S)
  have hc : Nat.card (center S) = 1 ∨ Nat.card (center S) = 2 := by omega
  rcases hc with hc | hc <;> simp [hc]

/-- Centerlessness is inherited from the component quotient; no model certification is needed. -/
theorem m24_elementary_sylow_fixer_card_le_two (hZ : center M24 = ⊥)
    (S : Sylow 2 M24) (A : Subgroup (MulAut M24)) [IsElementaryAbelian 2 A]
    (hfix : ∀ a ∈ A, ∀ x ∈ S, a x = x) : Nat.card A ≤ 2 := by
  let _ := m24_sylow_center_isCyclic S
  apply Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner S hZ _ A hfix
  intro a _ _
  obtain ⟨g, hg⟩ := M24OuterRestriction.conj_surjective a
  exact ⟨g, hg.symm⟩

end Sporadic.Mathieu
