module
public import Theory.GroupTheory.CentralExtensionSections
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.Alternating.proposition_5_2_7_8

/-!
# Splitting the prescribed fundamental SL₂ preimage

For odd q > 3 other than nine, the proved universal SL₂ → PSL₂ cover
splits every finite central extension of SL₂. At q = 9 the actual field
comparison PSL₂(F) ≃ A₆ and the exceptional multiplier bound show that
the derived cover's center has order dividing six. An odd kernel prime
to three is therefore trivial. At q = 3 Schur–Zassenhaus applies to the
coprime kernel and the base of order 24; no perfectness is asserted.

Each branch returns a section of the specified projection, which is
needed to identify the residual and image in `RootCoverTransfer`.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17, printed p.39; multiplier inputs I.1.3–I.1.4.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.RootCoverTransfer

/-- At q=9 the actual A₆ comparison bounds the derived preimage's center.
An odd kernel prime to three consequently disappears. -/
theorem exists_section_nine
    {E F : Type*} [Group E] [Finite E] [Field F] [Finite F]
    (hF : Nat.card F = 9) (f : E →* SL(2,F))
    (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (ho : Odd (Nat.card f.ker)) (h3 : Nat.Coprime 3 (Nat.card f.ker)) :
    ∃ s : SL(2,F) →* E, f.comp s = MonoidHom.id _ := by
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let d := CentralExtension.derivedCover f hf hc
  let : IsQuasisimple (commutator E) := d.isQuasisimple
  have hdc : Nat.card (center (commutator E)) ∣ 6 :=
    GLS3.Chapter5.exceptional_alternating_center_card_dvd_six 6
      (d.quotientCenterEquiv.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hF))
      (Or.inl rfl)
  let k : d.toMonoidHom.ker →* f.ker :=
    ((commutator E).subtype.comp d.toMonoidHom.ker.subtype).codRestrict _
      (fun x => x.property)
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : E)) h))
  have hkcard : Nat.card d.toMonoidHom.ker = 1 := by
    apply Nat.eq_one_of_dvd_coprimes
      (show Nat.Coprime 6 (Nat.card f.ker) from
        (Nat.coprime_two_left.mpr ho).mul_left h3)
    · exact (card_dvd_of_le d.ker_le_center).trans hdc
    · exact card_dvd_of_injective k hki
  let e := MulEquiv.ofBijective d.toMonoidHom
    ⟨d.toMonoidHom.ker_eq_bot_iff.mp (card_eq_one.mp hkcard), d.surjective⟩
  refine ⟨(commutator E).subtype.comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  exact e.apply_symm_apply x

/-- Every finite central extension of odd SL₂ by an odd defining-prime-free
kernel has a section of its prescribed projection, including q=3 and q=9. -/
theorem exists_section_sl2
    {E F : Type*} [Group E] [Finite E] [Field F] [Finite F]
    {r : ℕ} [Fact r.Prime] [CharP F r]
    (hF : Odd (Nat.card F)) (f : E →* SL(2,F))
    (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (ho : Odd (Nat.card f.ker)) (hr : Nat.Coprime r (Nat.card f.ker)) :
    ∃ s : SL(2,F) →* E, f.comp s = MonoidHom.id _ := by
  let : Fintype F := Fintype.ofFinite F
  have hsmall (h : Nat.card F = 3 ∨ Nat.card F = 9) : r = 3 := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hchar : CharP F 3 := by
      rcases h with h | h
      · exact charP_of_card_eq_prime (by simpa only [← Nat.card_eq_fintype_card] using h)
      · exact charP_of_card_eq_prime_pow (f := 2)
          (by simpa [← Nat.card_eq_fintype_card] using h)
    exact CharP.eq F ‹CharP F r› hchar
  by_cases h3 : Nat.card F = 3
  · apply CentralExtension.exists_section_of_coprime_kernel f hf
    rw [GorensteinWalter.sl2_card_formula F, h3]
    have hr3 : Nat.Coprime 3 (Nat.card f.ker) := hsmall (Or.inl h3) ▸ hr
    exact (show Nat.Coprime 24 (Nat.card f.ker) from
      ((Nat.coprime_two_left.mpr ho).pow_left 3).mul_left hr3).symm
  · by_cases h9 : Nat.card F = 9
    · exact exists_section_nine h9 f hf hc ho (hsmall (Or.inr h9) ▸ hr)
    · have hgt : 3 < Nat.card F := by
        have hpos : 1 < Nat.card F := Finite.one_lt_card
        have hn2 : Nat.card F ≠ 2 := by
          intro h
          rw [h] at hF
          exact (by decide : ¬ Odd 2) hF
        omega
      let : Fact (3 < Nat.card F) := ⟨hgt⟩
      exact CentralExtension.exists_section_of_universal_cover
        (GorensteinWalter.PSL2Cover.cover F)
        (CFSG.Quasithin.ChapterI.LieMultipliers.PSL2.odd_universalCover F hgt hF h9).1 f hf hc

end CFSG.Quasithin.ChapterA.Section02.RootCoverTransfer
