module

public import Theory.AlgebraicGroup.Borel.AdjointCenter

universe u

/-! Terminal semisimple isogenies and their centers. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- A terminal semisimple target has trivial center whenever a surjective
center-kernel morphism into a semisimple model with the same root-pairing type
is available. -/
public theorem center_eq_bot_of_terminal_isogeny_surjective_center_kernel
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    {Ka Q : Variety k} [AlgebraicGroup Ka] [AlgebraicGroup Q]
    (_hKaSemisimple : IsSemisimpleAlgebraicGroup Ka)
    (hKaTerminal : ∀ K : Variety k, ∀ _ : AlgebraicGroup K,
      IsSemisimpleAlgebraicGroup K → HasActualRootPairingType P K →
        ∃ φa : AlgebraicGroup.Morphism K Ka, IsIsogeny φa)
    (q : AlgebraicGroup.Morphism Ka Q)
    (hqSurjective : Function.Surjective q.onPoints)
    (hqKernel : q.kernel = Subgroup.center (Variety.Point Ka))
    (hQ : IsSemisimpleAlgebraicGroup Q)
    (hQRoot : HasActualRootPairingType P Q)
    (hcompInjective : ∀ (φ : AlgebraicGroup.Morphism Q Ka), IsIsogeny φ →
      Function.Injective (φ.comp q).onPoints) :
    Subgroup.center (Variety.Point Ka) = ⊥ := by
  obtain ⟨φ, hφ⟩ := hKaTerminal Q inferInstance hQ hQRoot
  let f : AlgebraicGroup.Morphism Ka Ka := φ.comp q
  have hfSurjective : Function.Surjective f.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := hφ.1 y
    obtain ⟨z, hz⟩ := hqSurjective x
    refine ⟨z, ?_⟩
    change φ.onPoints (q.onPoints z) = y
    rw [hz, hx]
  have hfInjective : Function.Injective f.onPoints :=
    hcompInjective φ hφ
  have hqInjective : Function.Injective q.onPoints := by
    intro x y hxy
    apply hfInjective
    change φ.onPoints (q.onPoints x) = φ.onPoints (q.onPoints y)
    rw [hxy]
  have hqKernelBot : q.kernel = ⊥ :=
    (MonoidHom.ker_eq_bot_iff q.onPoints).2 hqInjective
  calc
    Subgroup.center (Variety.Point Ka) = q.kernel := hqKernel.symm
    _ = ⊥ := hqKernelBot

end

end Theory.AlgebraicGroup
