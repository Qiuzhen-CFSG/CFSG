module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic
public import Theory.Representation.BinaryAlternatingSevenFixedPoints

/-!
# Excluding the four-space alternatives with the marked fixed seed

A three-cycle acts without fixed points in a faithful binary four-dimensional
A₇ representation. The existing proof reduces this to the explicit cubic
normal form recorded below. Applying it to both a representation and its dual
excludes the genuine four-plus-dual alternative whenever the marked L₀ fixes
a nonzero seed and contains a three-cycle. Equivariance is needed only for the
actual component inclusion; the two summands need not be H-invariant.

This is a conditional reduction: `CubicNormalForm` is an outstanding linear
algebra prerequisite, not an earlier chapter hypothesis. The NaturalSelection
assembly must discharge it, as well as construct the marked three-cycle.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959, and I.1.6(8),
printed p.408 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open PairsBranch.ModuleSelection

/-- The precise, independently owned linear algebra prerequisite. -/
def CubicNormalForm : Prop :=
  ∀ (F : Type) [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F],
    Module.finrank (ZMod 2) F = 4 → ∀ t : Module.End (ZMod 2) F,
      t ^ 3 = 1 → t ≠ 1 → (∃ v : F, v ≠ 0 ∧ t v = v) →
      ∃ basis : Module.Basis (Fin 4) (ZMod 2) F,
        LinearMap.toMatrix basis basis t = BinaryFourCubic.fixedPlaneMatrix

/-- The normal-form prerequisite supplies the intrinsic fixed-point calculation. -/
theorem threeCycle_fixedPointFree (hnormal : CubicNormalForm)
    {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) A7 F) (hσ : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) F = 4)
    (a : A7) (ha : Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)))
    (v : F) (hv : σ a v = v) : v = 0 :=
  binaryAlternatingSeven_threeCycle_fixedPointFree_of_normalForm σ hσ
    (hnormal F hdim) a ha v hv

private theorem dual_faithful {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) A7 F) (hσ : Function.Injective σ) :
    Function.Injective σ.dual := by
  intro a b hab
  apply inv_injective
  apply hσ
  apply (Module.dualMap_dualMap_eq_iff (ZMod 2) F).mp
  exact congrArg LinearMap.dualMap hab

variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E) (ι : A7 →* H)

/-- A nonzero vector fixed by the marked three-cycle excludes dimension four. -/
theorem not_four_of_fixed_threeCycle (hnormal : CubicNormalForm)
    (a : A7) (ha : Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)))
    (v : E) (hne : v ≠ 0) (hv : ρ (ι a) v = v) : ¬ IsFour ρ ι := by
  rintro ⟨σ, hσ, ⟨e⟩⟩
  have hf : σ a (e.symm v) = e.symm v := by
    exact (Representation.IntertwiningMap.isIntertwining (ρ.comp ι) σ
      e.symm.toIntertwiningMap a v).symm.trans (congrArg e.symm hv)
  have hz := threeCycle_fixedPointFree hnormal σ hσ
    (Module.finrank_fin_fun (ZMod 2)) a ha (e.symm v) hf
  exact hne (e.symm.injective (hz.trans (map_zero e.symm).symm))

/-- Both component constituents are treated, including the actual dual action. -/
theorem not_fourPlusDual_of_fixed_threeCycle (hnormal : CubicNormalForm)
    (a : A7) (ha : Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)))
    (v : E) (hne : v ≠ 0) (hv : ρ (ι a) v = v) : ¬ IsFourPlusDual ρ ι := by
  rintro ⟨σ, hσ, ⟨e⟩⟩
  have hf : (σ.prod σ.dual) a (e.symm v) = e.symm v := by
    exact (Representation.IntertwiningMap.isIntertwining (ρ.comp ι) (σ.prod σ.dual)
      e.symm.toIntertwiningMap a v).symm.trans (congrArg e.symm hv)
  have h₁ := threeCycle_fixedPointFree hnormal σ hσ
    (Module.finrank_fin_fun (ZMod 2)) a ha (e.symm v).1 (congrArg Prod.fst hf)
  have h₂ := threeCycle_fixedPointFree hnormal σ.dual (dual_faithful σ hσ)
    (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_fin_fun (ZMod 2))
    a ha (e.symm v).2 (congrArg Prod.snd hf)
  exact hne (e.symm.injective ((Prod.ext h₁ h₂).trans (map_zero e.symm).symm))

/-- Eliminate the genuine four and eight dimensional alternatives. The natural
identification uses the same seven-point map as the classification input. -/
theorem natural_of_fixed_threeCycle (φ : H →* Equiv.Perm (Fin 7))
    (hnormal : CubicNormalForm)
    (a : A7) (ha : Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)))
    (v : E) (hne : v ≠ 0) (hv : ρ (ι a) v = v)
    (halt : SmallModuleAlternatives ρ φ ι) : IsNatural ρ φ := by
  rcases halt with h4 | hn | h8
  · exact (not_four_of_fixed_threeCycle ρ ι hnormal a ha v hne hv h4).elim
  · exact hn
  · exact (not_fourPlusDual_of_fixed_threeCycle ρ ι hnormal a ha v hne hv h8).elim

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
