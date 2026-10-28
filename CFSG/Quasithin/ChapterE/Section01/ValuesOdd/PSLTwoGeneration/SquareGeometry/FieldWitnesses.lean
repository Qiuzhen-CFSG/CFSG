module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.EscapeTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.ActorGeometry

/-!
# The two field-image witness calculations

An actual involution with nontrivial field image gives, by projective-linear
conjugation, an isomorphic subgroup containing a pure field involution. When
there is no such involution the literal linear kernel is the canonical PSL₂
and all elementary actors lie in it. The assembly below proves that these
cases exhaust the quadratic field-image input of `SquareGeometry` and
transports the witnesses with their literal E-member conditions.

The two local calculations are explicit outstanding premises. This module
does not yet establish the field-image branch of E.1.14(6).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.2 and E.1.14(6), printed pp.210 and 214, citing Aschbacher (1982),
Lemma 4.10. The elementary-actor and involution reductions are in
`FieldWitnesses.ActorGeometry`.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses
universe u
variable {F : Type u} [Field F] [Finite F]

/-- The two concrete field-image branches exhaust the original model input.
The first calculation is on a subgroup containing a pure field involution;
the second retains nonsplit extensions and their literal linear kernel.
Both local calculations remain explicit prerequisites. -/
theorem largeFamilyEscape_of_involution_cases {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hlarge : 5 < p ^ 2)
    (hpure : ∀ (F : Type u) [Field F] [Finite F], Nat.card F = p ^ 2 →
      ∀ (S : Subgroup (PGammaL2 F)) [Finite S], pGammaL2PSLRange F ≤ S →
        ∀ σ : F ≃+* F, σ ^ 2 = 1 → σ ≠ 1 → SemidirectProduct.inr σ ∈ S →
          ∀ T : Sylow 2 S, LargeFamilyEscapeAt T)
    (hnonsplit : ∀ (F : Type u) [Field F] [Finite F], Nat.card F = p ^ 2 →
      ∀ (S : Subgroup (PGammaL2 F)) [Finite S], pGammaL2PSLRange F ≤ S →
        (pGammaL2LinearKernel F S).index = 2 →
        pGammaL2LinearKernel F S = (pGammaL2PSLRange F).subgroupOf S →
        (∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1) →
          ∀ T : Sylow 2 S, LargeFamilyEscapeAt T)
    (hF : Nat.card F = p ^ 2) (S : Subgroup (PGammaL2 F)) [Finite S]
    (hS : pGammaL2PSLRange F ≤ S) (hindex : (pGammaL2LinearKernel F S).index = 2) :
    ∀ T : Sylow 2 S, LargeFamilyEscapeAt T := by
  classical
  by_cases h : ∃ x : S, orderOf x = 2 ∧ pGammaL2FieldProjection F S x ≠ 1
  · obtain ⟨x, hx, hf⟩ := h
    obtain ⟨S', e, σ, hs, hn, hPSL, hσ⟩ :=
      exists_pureField_model_of_field_involution hp hodd hF hlarge S hS x hx hf
    let : Finite S' := Finite.of_equiv S e.toEquiv
    exact largeFamilyEscape_of_equiv e.symm (hpure F hF S' hPSL σ hs hn hσ)
  · have hno : ∀ x : S, orderOf x = 2 → pGammaL2FieldProjection F S x = 1 := by
      intro x hx
      by_contra hne
      exact h ⟨x, hx, hne⟩
    exact hnonsplit F hF S hS hindex
      (linearKernel_eq_inner_of_no_field_involutions hp hodd hF S hS hindex hno) hno

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses
