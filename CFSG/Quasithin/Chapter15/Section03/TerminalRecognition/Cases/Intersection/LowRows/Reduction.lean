module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.DirectProduct

/-!
# Exhausting the terminal nonquasisimple ambient rows

The nontrivial first local core excludes F.6.18(1) in either labeling.
Rows (4)–(13) contradict the nonquasisimplicity of the ambient generalized
Fitting subgroup. The S₃ × S₃ subcase of row (2) has already been proved.
The remaining output keeps the full supplied extraspecial extension and
prime-field product data, including both possible local labelings.

`RemainingRow` is a proved reduction output, not a classification premise.
Comparing its two constructors with the full B.5.6 action alternatives is
still needed to complete the nonquasisimple ambient branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; F.6.16–18, printed pp.308–310.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

namespace LowRows
universe u
variable {D : Type u} [Group D]

/-- The two unresolved row shapes, as an output of the full classification.
The product case keeps both possible local labelings. -/
inductive RemainingRow (G₁ G₂ : Subgroup D) (S : Sylow 2 D) : Prop
  | extraspecial (N : Subgroup D) (normal : N.Normal)
      (extraspecial : IsExtraspecial 3 N) (card : Nat.card N = 27)
      (exponent : Monoid.exponent N = 3)
      (quotient : Nonempty ((D ⧸ N) ≃* FSource.E4))
  | product (data : FSource.ProductRow S)
      (sylow : Nonempty (S ≃* DihedralGroup 4))
      (locals :
        (Nonempty (G₁ ≃* DihedralGroup 12) ∧ Nonempty (G₂ ≃* Equiv.Perm (Fin 4))) ∨
        (Nonempty (G₂ ≃* DihedralGroup 12) ∧ Nonempty (G₁ ≃* Equiv.Perm (Fin 4))))

private theorem RemainingRow.swap {G₁ G₂ : Subgroup D} {S : Sylow 2 D}
    (h : RemainingRow G₁ G₂ S) : RemainingRow G₂ G₁ S := by
  cases h with
  | extraspecial N hn he hc hx hq => exact .extraspecial N hn he hc hx hq
  | product c hs hl => exact .product c hs hl.symm

private theorem remaining_of_alternative {G₁ G₂ : Subgroup D} {S : Sylow 2 D}
    (hc : pCore 2 G₁ ≠ ⊥ ∨ pCore 2 G₂ ≠ ⊥)
    (hn : ¬ IsQuasisimple (generalizedFitting D))
    (h : FSource.Alternative G₁ G₂ S) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨ RemainingRow G₁ G₂ S := by
  cases h with
  | one _ hl hr _ => exact (hc.elim (fun h => h hl) (fun h => h hr)).elim
  | two hm =>
    rcases hm with hm | ⟨N, hN, he, hc, hx, hq⟩
    · exact Or.inl hm
    · exact Or.inr (.extraspecial N hN he hc hx hq)
  | three c hs hl hr => exact Or.inr (.product c hs (Or.inl ⟨hl, hr⟩))
  | four _ _ _ _ _ hq _ _ _ => exact (hn hq).elim
  | five _ _ _ _ _ hq _ _ _ => exact (hn hq).elim
  | six _ _ hq _ _ _ => exact (hn hq).elim
  | seven _ hq _ _ _ => exact (hn hq).elim
  | eight _ hq _ _ _ => exact (hn hq).elim
  | nine _ hq _ _ _ => exact (hn hq).elim
  | ten _ _ _ _ _ hq _ _ _ => exact (hn hq).elim
  | eleven _ hq _ _ _ => exact (hn hq).elim
  | twelve _ hq _ _ _ => exact (hn hq).elim
  | thirteen _ _ hq _ _ _ => exact (hn hq).elim

end LowRows

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H} (d : SourceInput V)

/-- Exhaust the thirteen F.6.18 rows in either local labeling. The direct
product row has its Thompson image identified; the two remaining shapes
retain all supplied extension, residual, action and local-group data. -/
theorem symmetricThree_or_remaining_low_rows
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection) d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection) d.quotientSylow)
    (hn : ¬ IsQuasisimple (generalizedFitting (coreQuotient H))) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      LowRows.RemainingRow (d.G1.map coreProjection) (d.G2.map coreProjection) d.quotientSylow := by
  rcases hF with hF | hF
  · rcases LowRows.remaining_of_alternative (Or.inl d.first_quotient_core_ne_bot) hn hF with
      he | h
    · obtain ⟨e⟩ := he
      exact Or.inl (d.thompson_symmetricThree_of_directProduct e)
    · exact Or.inr h
  · rcases LowRows.remaining_of_alternative (Or.inr d.first_quotient_core_ne_bot) hn hF with
      he | h
    · obtain ⟨e⟩ := he
      exact Or.inl (d.thompson_symmetricThree_of_directProduct e)
    · exact Or.inr h.swap

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
