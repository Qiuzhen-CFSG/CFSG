module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Binary
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.SmallSporadic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Held

/-!
# Finite-model branches in the field-component identification

The actual PSL₄(2)–A₈ equivalence excludes PSL₄(2). In degree five, the graph
case cannot fix a seven-element and an inner involution centralizer has
self-centralizing two-core. Thus both binary linear models are excluded.
Order and rank exclude
M₁₁, M₁₂ and J₁; the faithful normal two-kernel in the full involution
centralizer excludes M₂₃. All transports retain the ordinary component.

The marked Held 2B centralizer also has no ordinary component. The remaining
sporadic centralizer cases are not yet asserted.
In particular He remains in the source list, and J₂ always refers to the
sourced `Sporadic.LeechRelated.J2.Carrier`.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137, and Theorem C,
printed p.33, combined manuscript of 1 March 2004.
-/

public section

open Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

universe u
variable {S : Type u} [Group S] [Finite S] (s : SimpleInput S)
include s

/-- Exhaust the full eleven-model source list, retaining precisely the seven
branches not excluded here. This intermediate result retains He and the actual
J₂ carrier; the six unwanted centralizer branches still require proofs. -/
theorem SimpleInput.sporadic_remaining
    (h : ChapterA.Section02.IsTheoremCSporadicModel S) :
    Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (S ≃* M22) ∨ Nonempty (S ≃* M24) ∨
      Nonempty (S ≃* Janko4.Model) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (S ≃* Held.He) ∨ Nonempty (S ≃* Rudvalis.Model) := by
  rcases h with ⟨name, hname, hmodel⟩ | hmodel
  · cases name with
    | m11 => exact (s.not_m11 hmodel).elim
    | m12 => exact (s.not_m12 hmodel).elim
    | m22 => exact Or.inr (Or.inl hmodel)
    | m23 => exact (s.not_m23 hmodel).elim
    | m24 => exact Or.inr (Or.inr (Or.inl hmodel))
    | j2 => exact Or.inl hmodel
    | j3 => exact (hname rfl).elim
    | j4 => exact Or.inr (Or.inr (Or.inr (Or.inl hmodel)))
    | hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmodel))))
    | he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmodel)))))
    | ru => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmodel)))))
  · exact (s.not_j1 hmodel).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
