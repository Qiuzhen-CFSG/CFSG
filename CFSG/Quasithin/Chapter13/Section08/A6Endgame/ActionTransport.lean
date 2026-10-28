module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
import Mathlib.Tactic
/-!
# Equivariant transport of the point stabilizer

The point-parabolic model is transported through the duad action and the
binary natural module. The A₆ action here is the restriction of the specified
S₆ action. Comparing a source action to this model requires an explicit
equivariance identity, so its outer twist cannot be substituted just because
the dimensions agree. The actual point transporter is part of each model
equivalence, and its effect is proved to be conjugation by its inverse.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the terminal point-stabilizer argument on printed
pp. 968–969. This module does not construct the comparison for the source
five-dimensional cover or prove Lemma 13.8.34.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame

open Subgroup Theory.SpecificGroups.SymmetricSix

theorem stabilizer_transport {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (e : G ≃* H) (f : X ≃ Y)
    (heq : ∀ g x, f (g • x) = e g • f x) (x : X) :
    (MulAction.stabilizer G x).map e.toMonoidHom = MulAction.stabilizer H (f x) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    change e g • f x = f x
    rw [← heq, (show g • x = x from hg)]
  · intro hh
    obtain ⟨g, rfl⟩ := e.surjective h
    refine mem_map.mpr ⟨g, ?_, rfl⟩
    change g • x = x
    apply f.injective
    rw [heq]
    exact hh

noncomputable def stabilizerModel {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (e : G ≃* H) (f : X ≃ Y)
    (heq : ∀ g x, f (g • x) = e g • f x) (x : X) :
    MulAction.stabilizer G x ≃* MulAction.stabilizer H (f x) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (stabilizer_transport e f heq x))

noncomputable def duadStabilizerModel (x : Duad) (h : S6) (hx : h • (0 : Duad) = x) :
    MulAction.stabilizer S6 x ≃* duadStabilizer :=
  (MulAction.stabilizerEquivStabilizer hx.symm).symm.trans
    (MulEquiv.subgroupCongr duad_stabilizer_zero)

noncomputable def evenDuadStabilizerModel (x : Duad) (h : A6) (hx : h • (0 : Duad) = x) :
    MulAction.stabilizer A6 x ≃* a6DuadStabilizer :=
  (MulAction.stabilizerEquivStabilizer hx.symm).symm.trans
    (MulEquiv.subgroupCongr a6_duad_stabilizer_zero)

theorem polar_point_stabilizer (x : BinaryPoint) :
    MulAction.stabilizer S6 x = MulAction.stabilizer S6 (duadPolarEquiv.symm x) := by
  ext g
  change g • x = x ↔ g • duadPolarEquiv.symm x = duadPolarEquiv.symm x
  rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
  simp

theorem even_polar_point_stabilizer (x : BinaryPoint) :
    MulAction.stabilizer A6 x = MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
  ext g
  change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
  rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
  simp

noncomputable def polarPointModel (x : BinaryPoint) (h : S6)
    (hx : h • (0 : Duad) = duadPolarEquiv.symm x) :
    MulAction.stabilizer S6 x ≃* duadStabilizer :=
  (MulEquiv.subgroupCongr (polar_point_stabilizer x)).trans
    (duadStabilizerModel _ h hx)

noncomputable def evenPolarPointModel (x : BinaryPoint) (h : A6)
    (hx : h • (0 : Duad) = duadPolarEquiv.symm x) :
    MulAction.stabilizer A6 x ≃* a6DuadStabilizer :=
  (MulEquiv.subgroupCongr (even_polar_point_stabilizer x)).trans
    (evenDuadStabilizerModel _ h hx)


theorem polarPointModel_apply (x : BinaryPoint) (h : S6)
    (hx : h • (0 : Duad) = duadPolarEquiv.symm x)
    (z : MulAction.stabilizer S6 x) :
    (polarPointModel x h hx z).val = MulAut.conj h⁻¹ z.val := by
  exact MulAction.stabilizerEquivStabilizer_symm_apply hx.symm _

theorem evenPolarPointModel_apply (x : BinaryPoint) (h : A6)
    (hx : h • (0 : Duad) = duadPolarEquiv.symm x)
    (z : MulAction.stabilizer A6 x) :
    (evenPolarPointModel x h hx z).val = MulAut.conj h⁻¹ z.val := by
  exact MulAction.stabilizerEquivStabilizer_symm_apply hx.symm _

end CFSG.Quasithin.Chapter13.Section08.A6Endgame
