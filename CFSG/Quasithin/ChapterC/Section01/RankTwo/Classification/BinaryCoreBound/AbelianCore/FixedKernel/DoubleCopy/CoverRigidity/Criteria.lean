module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.Models

/-!+# Remaining model calculations for doubled-natural rigidity

The universal-cover calculation in `Models` reduces a nonzero kernel to
dimension one or two and identifies the latter case. The remaining independent
calculations are the identification of the one-dimensional-kernel cover and
the exclusion of FF-offenders for faithful overgroups normalizing the matrix
group on each of the two models. The predicates below specify obligations;
they are not asserted results or additional source hypotheses.

The conditional assembly discharges the dimension split. The unconditional
`DoubleCopy.CoverRigidity` still requires proofs of all three model obligations.
The source context is Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.34(2),(5), printed pp.136–137, and I.1.5–6, printed p.408. The offender
exclusion is an independent proposed argument, not a quoted MS93 lemma.
-/

@[expose] public section

open Representation Representation.OneCohomology

namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy

/-- The remaining cover classification: a one-dimensional covering kernel
gives one universal natural cover and one ordinary natural summand. -/
def CoverModels.MixedClassification.{u} : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) MatrixGroup W)
    (p : σ.IntertwiningMap natural), IsCover p →
    Module.finrank (ZMod 2) p.toLinearMap.ker = 1 → Nonempty (σ.Equiv CoverModels.mixed)

/-- The ambient offender obligation for an actual matrix-group module.
The equivalence concerns restriction to the normal matrix-group image;
the FF condition concerns the whole faithful overgroup action. -/
def CoverModels.NoFFOvergroups.{u, v} {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (τ : Representation (ZMod 2) MatrixGroup M) : Prop :=
  ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {H : Type v} [Group H] [Finite H]
    (δ : Representation (ZMod 2) H W) (ι : MatrixGroup →* H),
    Function.Injective δ → ι.range.Normal →
    Nonempty (Representation.Equiv (δ.comp ι) τ) → ¬ BinaryOffender.IsFFModule δ

/-- Conditional assembly of the independent model calculations. The kernel
dimension bound and the dimension-two identification are already proved;
the explicit model obligations must still be discharged. -/
theorem coverRigidity_of_model_results.{u, v}
    (hclass : CoverModels.MixedClassification.{u})
    (hmixed : CoverModels.NoFFOvergroups.{u, v} CoverModels.mixed)
    (hdoubled : CoverModels.NoFFOvergroups.{u, v} CoverModels.doubled) :
    CoverRigidity.{u, v} := by
  intro W _ _ _ H _ _ δ ι hδ hι p hp hFF
  by_contra hk
  rcases CoverModels.cover_kernel_finrank_cases p hp hk with h₁ | h₂
  · exact hmixed δ ι hδ hι (hclass (δ.comp ι) p hp h₁) hFF
  · exact hdoubled δ ι hδ hι
      (CoverModels.equiv_doubled_of_kernel_finrank_eq_two p hp h₂) hFF

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy
