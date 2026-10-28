module

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models

/-!
# Actual coordinates for the alternating-seven constituent

The four-dimensional A₇ row in B.4.2 supplies an actual group isomorphism
and a faithful action. Transport that action to binary four-space, retaining
both the linear intertwiner and the original group marking. This realizes
the separate A₇ disjunct in D.3.5(5); it does not identify it with natural A₆.
The chosen-seed application is in `SeedAlternativesMovedSylow`.

Source: Aschbacher--Smith B.4.2(7), D.3.5(5) and D.3.10(2),
combined manuscript of 1 March 2004, printed pp.86,195--196 and201.
-/

public noncomputable section

open Representation
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The faithful four-dimensional action itself, in binary coordinates,
supplies the A₇ constituent model with an actual intertwiner. -/
theorem constituentModel_of_alternatingSeven
    (ρ : Representation (ZMod 2) A W) (hf : Function.Injective ρ)
    (e : A ≃* alternatingGroup (Fin 7)) (hd : Module.finrank (ZMod 2) W = 4) :
    ConstituentModel ρ := by
  let b : W ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2) :=
    b.conjRingEquiv.toMonoidHom.comp (ρ.comp e.symm.toMonoidHom)
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨σ, ?_, ⟨e, b, ?_⟩⟩)))
  · exact b.conjRingEquiv.injective.comp (hf.comp e.symm.injective)
  · intro g v
    change b (ρ g v) = b (ρ (e.symm (e g)) (b.symm (b v)))
    rw [e.symm_apply_apply, b.symm_apply_apply]

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
