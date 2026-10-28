module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Bender
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Endpoints

/-!
# Characteristic-two part of the field-component identification

The full Bender catalogue, every even symplectic group, PSL₃(2), the actual
small derived symplectic carrier, and the actual Tits carrier are excluded
by proved subgroup obstructions. The remaining-alternatives theorem retains
every parameter restriction and actual model isomorphism.

The linear-three field-parameter calculation, both G₂ constructors, genuine
triality, and the Ree F₄ family remain to be proved. In particular this module
does not yet assert the rank-two PSL₃(4) identification.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of
15.3.38, printed p.1137; Theorem C and Remark A.2.4, printed p.33.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
variable {S : Type u} [Group S] [Finite S] (s : SimpleInput S)
include s

/-- Exhaustive reduction of all eight rank-two constructors after the proved
subgroup exclusions. The five displayed cases still need their fixed-component
calculations; this is not yet the PSL₃(4) identification. -/
theorem SimpleInput.even_rank_two_remaining {f : ℕ}
    (h : ChapterA.Section02.IsTheoremCRankTwoModel S f) :
    (2 ≤ f ∧ ClassicalGroup.IsPSL S 3 (2 ^ f)) ∨
    (2 ≤ f ∧ ClassificationModels.IsG2At S (2 ^ f)) ∨
    (1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2 ^ f) S) ∨
    (∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧ Nonempty (S ≃* ReeF4.Model m)) ∨
    (f = 1 ∧ Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2)))) := by
  cases h with
  | linear hf iso =>
    have hf2 : 2 ≤ f := by
      by_contra hn
      have he : f = 1 := by omega
      subst f
      exact s.not_binary_linear_three (by simpa only [pow_one] using iso)
    exact .inl ⟨hf2, iso⟩
  | symplectic _ iso => exact (s.not_even_symplectic iso).elim
  | g2 hf iso => exact .inr (.inl ⟨hf, iso⟩)
  | triality hf iso => exact .inr (.inr (.inl ⟨hf, iso⟩))
  | ree_f4 m hm hf iso => exact .inr (.inr (.inr (.inl ⟨m, hm, hf, iso⟩)))
  | symplectic_derived _ iso => exact (s.not_symplectic_derived iso).elim
  | g2_derived hf iso => exact .inr (.inr (.inr (.inr ⟨hf, iso⟩)))
  | tits _ iso => exact (s.not_tits iso).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
