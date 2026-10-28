module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.LinearModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.OtherModels

/-!
# Sieve for the intrinsic component models

The model calculations apply to a faithful elementary four-group fixing an
actual Sylow two-subgroup pointwise, with characteristic-two fixed subgroups.
Transport through each actual carrier equivalence lets those calculations
exclude the odd-center covers, A₇, the degree-three groups and M₁₂. The PSL₂
calculation retains the precise source parameters and leaves field size nine,
constructing A₆ and the S₆ inner extension of this same action.

`IntrinsicComponentModel` is the output contract of the outstanding lifting
step from I/O_{3′}(I) to its original component. It is not F.6.18, and must
not be supplied merely by a model label or by the quotient's isomorphism.
The unitary constructors retain the fixed-field order and the inherited
projective simplicity premise required by their concrete calculation.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, F.6.18,
printed pp.309–310, and the component paragraph of 15.4.18, pp.1162–1163.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch

/-- Intrinsic targets of the component-lifting step from the full F.6.18
quotient alternatives and 1.1.5. These are actual carrier identifications.
This predicate is not a replacement statement of the universal classification. -/
inductive IntrinsicComponentModel (L : Type*) [Group L] : Prop
  | linearTwo {F : Type} [Field F] [Finite F]
      (size : LinearModels.SourceFieldSize (Nat.card F)) (equiv : L ≃* PSL(2,F))
  | alternatingSix (equiv : L ≃* alternatingGroup (Fin 6))
  | tripleCover (center_card : Nat.card (center L) = 3)
  | alternatingSeven (equiv : L ≃* alternatingGroup (Fin 7))
  | linearSpecial (p : ℕ) [Fact p.Prime] (residue : p % 8 = 5)
      (equiv : L ≃* SL(3, ZMod p))
  | linearProjective (p : ℕ) [Fact p.Prime] (residue : p % 8 = 5)
      (equiv : L ≃* PSL(3, ZMod p))
  | unitarySpecial {E : Type} [Field E] [Finite E]
      (J : HermitianForm 3 E) (p : ℕ) (prime : p.Prime) (residue : p % 8 = 3)
      (field_card : Nat.card E = p ^ 2) (fixed_card : Nat.card {x : E // J.conj x = x} = p)
      (simple : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (equiv : L ≃* J.specialSubgroup)
  | unitaryProjective {E : Type} [Field E] [Finite E]
      (J : HermitianForm 3 E) (p : ℕ) (prime : p.Prime) (residue : p % 8 = 3)
      (field_card : Nat.card E = p ^ 2) (fixed_card : Nat.card {x : E // J.conj x = x} = p)
      (simple : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (equiv : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  | mathieuTwelve (equiv : L ≃* Sporadic.Mathieu.M12)

private theorem FixedAction.no_obstruction {L A : Type*} [Group L] [Group A]
    (d : FixedAction L A)
    (h : ∃ a : A, a ≠ 1 ∧ ¬ HasCharacteristicTwo (d.action a).fixedSubgroup) : False := by
  obtain ⟨a, ha, hc⟩ := h
  exact hc (d.characteristicTwo a ha)

/-- The intrinsic models and the actual fixed action leave only A₆ and its
S₆ inner extension. All non-PSL₂ alternatives are eliminated using their
proved fixed-subgroup obstructions; the PSL₂ parameters force field size nine. -/
theorem FixedAction.select_alternatingSix
    {L A : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (d : FixedAction L A) (hA : Nat.card A = 4) (model : IntrinsicComponentModel L) :
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∧
      Nonempty (MulAut.innerExtension d.action ≃* Equiv.Perm (Fin 6)) := by
  cases model with
  | linearTwo hsize e =>
    let f := d.transport e
    obtain ⟨eL, eS, _, _⟩ := LinearModels.exists_symmetric_extension_of_sourceFieldSize
      hsize f.sylow f.action f.faithful hA f.fixes f.characteristicTwo
    exact ⟨⟨e.trans eL⟩, ⟨(MulAut.innerExtensionCongr e d.action).trans eS⟩⟩
  | alternatingSix e =>
    let f := d.transport e
    let eS := AlternatingSix.ShadowLocal.sylowFixedExtensionEquiv
      f.sylow f.action f.faithful hA f.fixes
    exact ⟨⟨e⟩, ⟨(MulAut.innerExtensionCongr e d.action).trans eS⟩⟩
  | tripleCover hZ =>
    exact (d.no_obstruction
      (OtherModels.center_three_fixed_action_obstruction hZ hA d.action)).elim
  | alternatingSeven e =>
    let f := d.transport e
    exact (f.no_obstruction (OtherModels.alternating_seven_fixed_action_obstruction
      f.sylow hA f.action f.faithful f.fixes)).elim
  | linearSpecial p hp e =>
    let f := d.transport e
    exact (f.no_obstruction (OtherModels.linearThree_special_fixed_action_obstruction
      p hp f.sylow hA f.action f.faithful (fun a x => f.fixes a x x.property))).elim
  | linearProjective p hp e =>
    let f := d.transport e
    exact (f.no_obstruction (OtherModels.linearThree_projective_fixed_action_obstruction
      p hp f.sylow hA f.action f.faithful (fun a x => f.fixes a x x.property))).elim
  | unitarySpecial J p hp hm hE hfix hs e =>
    let := hs
    let : Group.IsPerfect J.specialSubgroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let f := d.transport e
    exact (f.no_obstruction (OtherModels.special_unitary_fixed_action_obstruction
      J hp hm hE hfix f.sylow hA f.action f.faithful
      (fun a x => f.fixes a x x.property))).elim
  | unitaryProjective J p hp hm hE hfix hs e =>
    let := hs
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let f := d.transport e
    exact (f.no_obstruction (OtherModels.projective_unitary_fixed_action_obstruction
      J hp hm hE hfix f.sylow hA f.action f.faithful
      (fun a x => f.fixes a x x.property))).elim
  | mathieuTwelve e =>
    let f := d.transport e
    exact (f.no_obstruction (OtherModels.mathieuTwelve_fixed_action_obstruction_unconditional
      f.sylow hA f.action f.faithful (fun a x => f.fixes a x x.property))).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch
