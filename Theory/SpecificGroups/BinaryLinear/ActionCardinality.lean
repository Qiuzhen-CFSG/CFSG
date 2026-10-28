module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.Representation.GeneralLinearNatural

/-!
# Orders of binary linear groups and quotient spaces

The usual product formula computes the order in a prescribed binary degree.
A complement to a subspace embeds the full linear group of its quotient into
the full linear group of the original space. Thus a full representation has
an actor at least as large as either of those linear groups.

These estimates exclude the nonnatural rows in Aschbacher–Smith 12.2.20,
printed p.802, by comparison with the seven rows of 12.2.2(3), p.795.
-/

@[expose] public noncomputable section
namespace BinaryLinear
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

def order (n : ℕ) : ℕ := ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ))

theorem card_GL_of_finrank {n : ℕ} (hd : Module.finrank (ZMod 2) W = n) :
    Nat.card (BinaryLinear.GL W) = order n := by
  let b : Module.Basis (Fin n) (ZMod 2) W := (Module.finBasis (ZMod 2) W).reindex (finCongr hd)
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simp only [ZMod.card, order]

theorem card_SL (n : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = order n := by
  rw [Nat.card_congr (OuterCyclic.slEquivLinear n).toEquiv]
  exact card_GL_of_finrank (by simp [OuterCyclic.Space])

theorem card_GL_quotient_le (P : Submodule (ZMod 2) W) :
    Nat.card (BinaryLinear.GL (W ⧸ P)) ≤ Nat.card (BinaryLinear.GL W) := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL W) :=
    Finite.of_injective (fun a : BinaryLinear.GL W => (a : W → W)) DFunLike.coe_injective
  obtain ⟨e⟩ := quotient_prod_linearEquiv P
  let f (a : BinaryLinear.GL (W ⧸ P)) : BinaryLinear.GL W :=
    e.symm.trans ((a.prodCongr (LinearEquiv.refl (ZMod 2) P)).trans e)
  apply Nat.card_le_card_of_injective f
  intro a b hab
  apply LinearEquiv.ext
  intro v
  have he := congrArg (fun g : BinaryLinear.GL W => (e.symm (g (e (v, 0)))).1) hab
  simpa [f] using he

omit [FiniteDimensional (ZMod 2) W] in
theorem card_GL_le_of_full {A : Type*} [Group A] [Finite A]
    (ρ : Representation (ZMod 2) A W)
    (hf : Function.Surjective ((LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom)) :
    Nat.card (BinaryLinear.GL W) ≤ Nat.card A := Nat.card_le_card_of_surjective _ hf

end BinaryLinear
