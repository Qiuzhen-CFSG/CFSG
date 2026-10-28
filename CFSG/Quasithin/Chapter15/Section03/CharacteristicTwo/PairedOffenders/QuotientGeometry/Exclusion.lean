module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Coordinates

/-!
# Exclusion from the block kernel

For every conjugate of the even pair subgroup, evaluation on one point in each
block embeds its intersection with the block kernel in a set of order four.
This excludes its eight elements from that kernel. Together with parity and
transitivity this excludes all four actual offender families, without choosing
representatives for the conjugates.

Source: Aschbacher–Smith, proof of 15.3.25, printed p.1133.
-/

public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

private theorem blockCore_ext {a b : Perm} (ha : a ∈ blockCore) (hb : b ∈ blockCore)
    (h0 : a 0 = b 0) (h4 : a 4 = b 4) : a = b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have ht : ∀ i j, coreWords i 0 = coreWords j 0 → coreWords i 4 = coreWords j 4 →
      coreWords i = coreWords j := by decide +kernel
  exact ht i j h0 h4

private theorem D_preserves_pairs {a : Perm} (ha : a ∈ D 8) (x : Fin 8) :
    (a x).val / 2 = x.val / 2 := by
  obtain ⟨i, rfl⟩ := (mem_D_iff a).mp ha
  have ht : ∀ i x, (dWords i x).val / 2 = x.val / 2 := by decide +kernel
  exact ht i x

/-- Evaluation on one point from each four-point block embeds a pair-orbit
subgroup of the block kernel into a product of two sets of size two. -/
theorem card_le_four_of_le_blockCore_conjugate_D {A : Subgroup Perm}
    (hA : A ≤ blockCore) (g : Perm) (hD : A ≤ (D 8).map (MulAut.conj g).toMonoidHom) :
    Nat.card A ≤ 4 := by
  let f : A → Fin 2 × Fin 2 := fun a =>
    (⟨(g⁻¹ (a.val 0)).val % 2, Nat.mod_lt _ (by decide)⟩,
     ⟨(g⁻¹ (a.val 4)).val % 2, Nat.mod_lt _ (by decide)⟩)
  have hp (a : A) (x : Fin 8) : (g⁻¹ (a.val x)).val / 2 = (g⁻¹ x).val / 2 := by
    obtain ⟨d, hd, he⟩ := hD a.property
    have hx : g⁻¹ (a.val x) = d (g⁻¹ x) := by
      rw [← he]
      change g⁻¹ (g (d (g⁻¹ x))) = _
      exact g.symm_apply_apply _
    rw [hx]
    exact D_preserves_pairs hd _
  have hi : Function.Injective f := by
    intro a b he
    have h0 := congrArg (fun y : Fin 2 × Fin 2 => y.1.val) he
    have h4 := congrArg (fun y : Fin 2 × Fin 2 => y.2.val) he
    change (g⁻¹ (a.val 0)).val % 2 = (g⁻¹ (b.val 0)).val % 2 at h0
    change (g⁻¹ (a.val 4)).val % 2 = (g⁻¹ (b.val 4)).val % 2 at h4
    apply Subtype.ext
    apply blockCore_ext (hA a.property) (hA b.property)
    · apply g.symm.injective
      apply Fin.ext
      change (g⁻¹ (a.val 0)).val = (g⁻¹ (b.val 0)).val
      have := hp a 0
      have := hp b 0
      omega
    · apply g.symm.injective
      apply Fin.ext
      change (g⁻¹ (a.val 4)).val = (g⁻¹ (b.val 4)).val
      have := hp a 4
      have := hp b 4
      omega
  simpa using Nat.card_le_card_of_injective f hi

/-- The even case is excluded for every conjugate, with no Sylow-position
hypothesis. Its eight elements cannot fit the two independent pair orbits
available inside the Klein-four product. -/
theorem even_not_le_blockCore {A : Subgroup Perm}
    (hA : EightCase.even.Realizes A) : ¬ A ≤ blockCore := by
  obtain ⟨g, rfl⟩ := hA
  intro h
  have hb := card_le_four_of_le_blockCore_conjugate_D h g (map_mono inf_le_left)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_evenPart] at hb
  omega

/-- None of the four actual permutation families lies in the block kernel. -/
theorem realizes_not_le_blockCore {c : EightCase} {A : Subgroup Perm}
    (hA : c.Realizes A) : ¬ A ≤ blockCore := by
  cases c with
  | regular => exact regular_not_le_blockCore hA
  | transposition => exact transposition_not_le_blockCore hA
  | disjoint => exact disjoint_not_le_blockCore hA
  | even => exact even_not_le_blockCore hA
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
