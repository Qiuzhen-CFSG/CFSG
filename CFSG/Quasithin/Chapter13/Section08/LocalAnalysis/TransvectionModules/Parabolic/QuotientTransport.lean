module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad

/-!
# Transport of the marked parabolic quotient

A surjection onto either actual six-letter duad parabolic, with two-group
kernel, identifies the quotient by the source two-core with S₃. The proof
uses the explicit model homomorphism and lifts its two-core through the
surjection. In particular the kernel is proved to be the full two-core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the parabolic
step in 13.8.6(1), printed p.948. Constructing the surjection from K₂T,
with the source marking and the required kernel, is an application premise.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic

open Subgroup Theory.SpecificGroups.SymmetricSix

variable {P : Type*} [Group P] [Finite P]

/-- Lift the S₆ duad-parabolic quotient across a two-group kernel. -/
noncomputable def duadQuotientOfTwoKernel (f : P →* duadStabilizer)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    P ⧸ pCore 2 P ≃* Equiv.Perm (Fin 3) := by
  let q := duadQuotientHom.comp f
  have hq : Function.Surjective q := duadQuotientHom_surjective.comp hf
  have hk : q.ker = pCore 2 P := by
    change duadQuotientHom.ker.comap f = pCore 2 P
    rw [duadQuotientHom_ker]
    exact f.comap_pCore_of_ker_isPGroup hf hker
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

/-- Lift the A₆ duad-parabolic quotient across a two-group kernel. -/
noncomputable def a6DuadQuotientOfTwoKernel (f : P →* a6DuadStabilizer)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    P ⧸ pCore 2 P ≃* Equiv.Perm (Fin 3) := by
  let q := a6DuadQuotientHom.comp f
  have hq : Function.Surjective q := a6DuadQuotientHom_surjective.comp hf
  have hk : q.ker = pCore 2 P := by
    change a6DuadQuotientHom.ker.comap f = pCore 2 P
    rw [a6DuadQuotientHom_ker]
    exact f.comap_pCore_of_ker_isPGroup hf hker
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic
