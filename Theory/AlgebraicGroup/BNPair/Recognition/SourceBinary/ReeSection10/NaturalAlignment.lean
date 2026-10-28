module
public import Theory.Representation.Suzuki.NaturalCentralizer

/-!
# Scalar alignment of the Section 10 natural intertwiners

The two choices of a faithful natural-module intertwiner are not independent:
their quotient commutes with the literal Suzuki action and hence is scalar.
This is the normalization step needed before comparing the distinguished root
lines in (10.7)--(10.9).  The result is stated for the actual matrix action and
keeps the field scalar explicit; it does not identify any source subgroup with
a model.

Source: Fong--Seitz II (1974), pp.222--224, equations (10.7)--(10.9).
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups
open Representation
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10

/-- The quotient of two natural-module intertwiners, regarded as an additive
map on the literal natural module. -/
def intertwinerQuotient {m : ℕ} {V : Type*}
    [AddCommMonoid V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (e₁ e₂ : ρ.Equiv (Representation.SuzukiNatural.natural m)) :
    Representation.SuzukiNatural.W m →+ Representation.SuzukiNatural.W m :=
  (e₂.toLinearEquiv.toLinearMap.toAddMonoidHom).comp
    (e₁.toLinearEquiv.symm.toLinearMap.toAddMonoidHom)

private theorem intertwinerQuotient_apply {m : ℕ} {V : Type*}
    [AddCommMonoid V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (e₁ e₂ : ρ.Equiv (Representation.SuzukiNatural.natural m))
    (v : Representation.SuzukiNatural.W m) :
    intertwinerQuotient ρ e₁ e₂ v = e₂.toLinearEquiv (e₁.toLinearEquiv.symm v) := rfl

private theorem intertwinerQuotient_commutes {m : ℕ} {V : Type*}
    [AddCommMonoid V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (e₁ e₂ : ρ.Equiv (Representation.SuzukiNatural.natural m))
    (g : SuzukiMatrixGroup m) (v : Representation.SuzukiNatural.W m) :
    intertwinerQuotient ρ e₁ e₂ ((Representation.SuzukiNatural.natural m) g v) =
      (Representation.SuzukiNatural.natural m) g
        (intertwinerQuotient ρ e₁ e₂ v) := by
  rw [intertwinerQuotient_apply, intertwinerQuotient_apply]
  have h₁ := e₁.toIntertwiningMap.isIntertwining' g
  have h₂ := e₂.toIntertwiningMap.isIntertwining' g
  have hi : ρ g (e₁.toLinearEquiv.symm v) = e₁.toLinearEquiv.symm
      ((Representation.SuzukiNatural.natural m) g v) := by
    have hh := congrArg (fun z => z (e₁.toLinearEquiv.symm v)) h₁
    change e₁.toLinearEquiv (ρ g (e₁.toLinearEquiv.symm v)) =
      (Representation.SuzukiNatural.natural m) g
        (e₁.toLinearEquiv (e₁.toLinearEquiv.symm v)) at hh
    rw [e₁.toLinearEquiv.apply_symm_apply] at hh
    have hh' : e₁.toLinearEquiv (ρ g (e₁.toLinearEquiv.symm v)) =
        (Representation.SuzukiNatural.natural m) g v := hh
    simpa only [LinearEquiv.symm_apply_apply] using congrArg e₁.toLinearEquiv.symm hh'
  rw [← hi]
  have hh := congrArg (fun z => z (e₁.toLinearEquiv.symm v)) h₂
  change e₂.toLinearEquiv (ρ g (e₁.toLinearEquiv.symm v)) =
    (Representation.SuzukiNatural.natural m) g
      (e₂.toLinearEquiv (e₁.toLinearEquiv.symm v)) at hh
  exact hh

/-- Any two faithful natural intertwiners differ by multiplication by a single
nonzero coefficient.  The scalar acts on all four natural coordinates at once. -/
theorem natural_intertwiner_scalar_unique {m : ℕ} {V : Type*}
    [AddCommMonoid V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V)
    (e₁ e₂ : ρ.Equiv (Representation.SuzukiNatural.natural m)) :
    ∃ a : Representation.SuzukiNatural.F m, a ≠ 0 ∧ ∀ v : V,
      e₂.toLinearEquiv v = a • e₁.toLinearEquiv v := by
  let f := intertwinerQuotient ρ e₁ e₂
  obtain ⟨a, ha⟩ := Representation.SuzukiNatural.commuting_addHom_eq_scalar m f
    (fun g v => intertwinerQuotient_commutes ρ e₁ e₂ g v)
  have hne : a ≠ 0 := by
    intro haz
    have hz : f (![1, 0, 0, 0] : Representation.SuzukiNatural.W m) = 0 := by
      rw [ha, haz, zero_smul]
    have hfzero : f (![1, 0, 0, 0] : Representation.SuzukiNatural.W m) = f 0 := by
      exact hz.trans (map_zero f).symm
    have hf : Function.Injective f :=
      e₂.toLinearEquiv.injective.comp e₁.toLinearEquiv.symm.injective
    have hvec : (![1, 0, 0, 0] : Representation.SuzukiNatural.W m) = 0 := hf hfzero
    have hcoord := congrFun hvec 0
    simp only [Pi.zero_apply, Matrix.cons_val_zero, one_ne_zero] at hcoord
  refine ⟨a, hne, ?_⟩
  intro v
  have hv := ha (e₁.toLinearEquiv v)
  change e₂.toLinearEquiv (e₁.toLinearEquiv.symm (e₁.toLinearEquiv v)) = _ at hv
  simpa only [LinearEquiv.symm_apply_apply] using hv

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
