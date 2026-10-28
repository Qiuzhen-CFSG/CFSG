module
public import Theory.Representation.BinaryOffender.InvolutionRatio

/-!
# Involution fixed vectors outside a small kernel

An involution of a binary module fixes at least half the full space. If a
subspace has dimension at most two and quotient dimension four, its fixed
space cannot be contained in that subspace. Source application: the original
natural and deleted A₅ factors in Aschbacher–Smith 10.2.12, printed p.754.
-/

public section
open Representation Subgroup
namespace Representation.BinaryOffender

variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A binary involution fixes a vector outside every kernel of degree at most two
whose quotient has degree four.
The statement is phrased for the actual full actor representation, so no
identification of that actor with A₅ is made. -/
theorem exists_fixed_outside_of_finrank_quotient_four
    (τ : Representation (ZMod 2) A W) (b : A) (hb : orderOf b = 2)
    (Z : Submodule (ZMod 2) W)
    (hZ : Module.finrank (ZMod 2) Z ≤ 2)
    (hquot : Module.finrank (ZMod 2) W = 4 + Module.finrank (ZMod 2) Z) :
    ∃ w : W, w ∈ fixedSpace τ (zpowers b) ∧ w ∉ Z := by
  by_contra! hnone
  have hfix : fixedSpace τ (zpowers b) ≤ Z := hnone
  have hbound := involution_actor_rank_and_fixedCodim τ b hb
  have hdim := fixedCodim_add_finrank τ (zpowers b)
  have hfixed : Module.finrank (ZMod 2) (fixedSpace τ (zpowers b)) ≤
      Module.finrank (ZMod 2) Z :=
    Submodule.finrank_mono hfix
  omega

end Representation.BinaryOffender
