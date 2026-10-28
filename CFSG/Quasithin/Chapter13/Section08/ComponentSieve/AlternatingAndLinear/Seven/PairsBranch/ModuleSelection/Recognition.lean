module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic

/-!
# B.3/B.4 inputs with the fixed seven-point marking

The universal strong-FF exclusion and transvection-recognition consequences
are explicit earlier inputs. They quantify over actual subgroups between A₇
and S₇, arbitrary finite-dimensional binary representations, faithfulness,
and, for recognition, a nonidentity involution with fixed codimension one.
The standard reductions from B.4's component-irreducible statements to these
consequences are part of those inputs, not asserted as proved in this module.

For a faithful φ the group H is isomorphic to its literal permutation image.
Transport along this equivalence preserves elementary subgroup ranks and
fixed codimensions. Pulling back the recognized embedding preserves the same
φ in its equivariance equation. Specializing to the literal W and quotient
gives exactly the four functions required by `Sieve.rank_one_and_natural_sections`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1, B.3, B.4.2 and B.4.5, and their application in 13.8.24,
printed p.959/PDF p.976 (1 March 2004 manuscript).
-/

@[expose] public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
universe u

/-- Explicit universal B.1/B.4 consequence, for actual intermediate permutation
groups and arbitrary faithful finite-dimensional modules. -/
def SevenPointNoStrongInput : Prop :=
  ∀ (J : Subgroup (Equiv.Perm (Fin 7))), alternatingGroup (Fin 7) ≤ J →
  ∀ (F : Type u) [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) J F), Function.Injective σ → ¬ IsStrongFFModule σ

/-- Explicit universal B.3/B.4 recognition consequence. All representations,
transvection involutions, and seven-point markings are literal. -/
def SevenPointRecognitionInput : Prop :=
  ∀ (J : Subgroup (Equiv.Perm (Fin 7))), alternatingGroup (Fin 7) ≤ J →
  ∀ (F : Type u) [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) J F), Function.Injective σ →
    ∀ a : J, a ≠ 1 → a ^ 2 = 1 → fixedCodim σ (zpowers a) = 1 →
      HasNaturalSubmodule σ J.subtype

variable {H : Type*} [Group H] {E : Type u} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E) (φ : H →* Equiv.Perm (Fin 7))
  (hφ : Function.Injective φ) (K : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))

include hK in
private theorem alternating_le_range : alternatingGroup (Fin 7) ≤ φ.range := by
  rw [← hK]
  rintro g ⟨k, _, hk⟩
  exact ⟨k, hk⟩

include hφ hK in
/-- Pull the universal exclusion back along the actual faithful seven-point map.
This specializes directly to either literal section used by Sieve. -/
theorem noStrong_of_permutation_input (hinput : SevenPointNoStrongInput.{u})
    (hρ : Function.Injective ρ) : ¬ IsStrongFFModule ρ := by
  let e : H ≃* φ.range := MonoidHom.ofInjective hφ
  let σ : Representation (ZMod 2) φ.range E := ρ.comp e.symm.toMonoidHom
  have he (g : H) (v : E) : ρ g v = σ (e g) v := by
    change ρ g v = ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]
  have hσ : Function.Injective σ := hρ.comp e.symm.injective
  have hn := hinput φ.range (alternating_le_range φ K hK) E σ hσ
  rintro ⟨A, hA, hlt⟩
  have hw := (show IsOffender ρ A from ⟨hA, hlt.le⟩).map_equivariant
    ρ σ e.toMonoidHom e.injective (LinearEquiv.refl _ _) he
  apply hn
  refine ⟨A.map e.toMonoidHom, hw.1, ?_⟩
  rw [← fixedCodim_map_equivariant ρ σ e.toMonoidHom (LinearEquiv.refl _ _) he,
    rank_map_injective e.toMonoidHom e.injective]
  exact hlt

include hφ hK in
/-- Recognition preserves the very same φ after the acting-group transport. -/
theorem recognition_of_permutation_input (hinput : SevenPointRecognitionInput.{u})
    (hρ : Function.Injective ρ) (a : H) (hne : a ≠ 1) (hpow : a ^ 2 = 1)
    (hc : fixedCodim ρ (zpowers a) = 1) : HasNaturalSubmodule ρ φ := by
  let e : H ≃* φ.range := MonoidHom.ofInjective hφ
  let σ : Representation (ZMod 2) φ.range E := ρ.comp e.symm.toMonoidHom
  have he (g : H) (v : E) : ρ g v = σ (e g) v := by
    change ρ g v = ρ (e.symm (e g)) v
    rw [e.symm_apply_apply]
  have hσ : Function.Injective σ := hρ.comp e.symm.injective
  have hne' : e a ≠ 1 := fun hz => hne (e.injective (hz.trans e.map_one.symm))
  have hpow' : (e a) ^ 2 = 1 := by rw [← map_pow, hpow, map_one]
  have hc' : fixedCodim σ (zpowers (e a)) = 1 := by
    change fixedCodim σ (zpowers (e.toMonoidHom a)) = 1
    rw [← MonoidHom.map_zpowers e.toMonoidHom a,
      ← fixedCodim_map_equivariant ρ σ e.toMonoidHom (LinearEquiv.refl _ _) he]
    exact hc
  obtain ⟨j, hj, heq⟩ := hinput φ.range (alternating_le_range φ K hK) E σ hσ
    (e a) hne' hpow' hc'
  refine ⟨j, hj, ?_⟩
  intro g v
  exact (heq (e g) v).trans (he g (j v)).symm

include hφ hK in
/-- All four functions expected by Sieve, for the literal W and literal quotient. -/
theorem sieve_inputs (hn : SevenPointNoStrongInput.{u})
    (hr : SevenPointRecognitionInput.{u}) (W : Subrepresentation ρ) :
    (Function.Injective W.toRepresentation → ¬ IsStrongFFModule W.toRepresentation) ∧
    (Function.Injective W.quotientRepresentation → ¬ IsStrongFFModule W.quotientRepresentation) ∧
    (Function.Injective W.toRepresentation → ∀ a : H, a ≠ 1 → a ^ 2 = 1 →
      fixedCodim W.toRepresentation (zpowers a) = 1 → HasNaturalSubmodule W.toRepresentation φ) ∧
    (Function.Injective W.quotientRepresentation → ∀ a : H, a ≠ 1 → a ^ 2 = 1 →
      fixedCodim W.quotientRepresentation (zpowers a) = 1 →
        HasNaturalSubmodule W.quotientRepresentation φ) := by
  exact ⟨noStrong_of_permutation_input W.toRepresentation φ hφ K hK hn,
    noStrong_of_permutation_input W.quotientRepresentation φ hφ K hK hn,
    recognition_of_permutation_input W.toRepresentation φ hφ K hK hr,
    recognition_of_permutation_input W.quotientRepresentation φ hφ K hK hr⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
