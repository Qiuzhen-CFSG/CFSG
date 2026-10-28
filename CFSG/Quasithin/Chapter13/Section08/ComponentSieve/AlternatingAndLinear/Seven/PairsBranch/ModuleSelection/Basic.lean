module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Seed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.Partitions
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The three representation alternatives for the pair branch

The four-dimensional alternatives carry actual faithful representations of A₇.
The eight-dimensional alternative is their product with the contragredient,
identified equivariantly with the restriction to the same component inclusion.
The natural alternative is an equivariant identification for the whole H-action
and the specified seven-point homomorphism. Thus an outer element may exchange
the four-dimensional summands; no H-invariance of either summand is imposed.

`FourPlaneExclusion` states the finite calculation for the actual partition
stabilizer, proved in the extension module `ModuleSelection.FourSpace`. The
module-selection assembly uses that proof to eliminate both exceptional
alternatives.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.2(7), B.4.5, printed pp.86–87, and 13.8.24, printed p.959,
PDF p.976 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
open Representation Representation.BinaryOffender

abbrev A7 := alternatingGroup (Fin 7)
abbrev Four := Fin 4 → ZMod 2

/-- The even part of the genuine partition stabilizer. -/
def evenPairStabilizer : Subgroup A7 := pairStabilizer.comap (alternatingGroup (Fin 7)).subtype

/-- The precise finite representation calculation needed to exclude both
exceptional alternatives. It quantifies over all faithful four-dimensional
actions, including the contragredient, and not over a family tag. -/
def FourPlaneExclusion : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) A7 V), Function.Injective σ →
    Module.finrank (ZMod 2) V = 4 → ∀ S : Submodule (ZMod 2) V,
    Module.finrank (ZMod 2) S = 2 → evenPairStabilizer ≤ subspaceStabilizer σ S → False

variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- A compatible identification with the binary natural seven-point module. -/
def IsNatural (ρ : Representation (ZMod 2) H E) (φ : H →* Equiv.Perm (Fin 7)) : Prop :=
  Nonempty (Representation.Equiv ((BinaryPermutation.coreRepresentation (Fin 7)).comp φ) ρ)

/-- An actual four-dimensional component representation, in binary coordinates. -/
def IsFour (ρ : Representation (ZMod 2) H E) (ι : A7 →* H) : Prop :=
  ∃ σ : Representation (ZMod 2) A7 Four, Function.Injective σ ∧
    Nonempty (σ.Equiv (ρ.comp ι))

/-- The two component constituents are a four-space and its actual dual.
Equivariance is required only for K, as in the source's irreducible H-module. -/
def IsFourPlusDual (ρ : Representation (ZMod 2) H E) (ι : A7 →* H) : Prop :=
  ∃ σ : Representation (ZMod 2) A7 Four, Function.Injective σ ∧
    Nonempty ((σ.prod σ.dual).Equiv (ρ.comp ι))

/-- No B.4 alternative has yet been discarded. -/
def SmallModuleAlternatives (ρ : Representation (ZMod 2) H E)
    (φ : H →* Equiv.Perm (Fin 7)) (ι : A7 →* H) : Prop :=
  IsFour ρ ι ∨ IsNatural ρ φ ∨ IsFourPlusDual ρ ι

/-- The actual component identification induced by the fixed seven-point map. -/
noncomputable def componentEquiv (φ : H →* Equiv.Perm (Fin 7))
    (hφ : Function.Injective φ) (K : Subgroup H)
    (hK : K.map φ = alternatingGroup (Fin 7)) : K ≃* A7 :=
  (K.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hK)

/-- The inverse component identification, as an inclusion in H. -/
noncomputable def componentInclusion (φ : H →* Equiv.Perm (Fin 7))
    (hφ : Function.Injective φ) (K : Subgroup H)
    (hK : K.map φ = alternatingGroup (Fin 7)) : A7 →* H :=
  K.subtype.comp (componentEquiv φ hφ K hK).symm.toMonoidHom

/-- This inclusion has exactly the required seven-point marking. -/
theorem componentInclusion_compatible (φ : H →* Equiv.Perm (Fin 7))
    (hφ : Function.Injective φ) (K : Subgroup H)
    (hK : K.map φ = alternatingGroup (Fin 7)) (a : A7) :
    φ (componentInclusion φ hφ K hK a) = a :=
  congrArg Subtype.val ((componentEquiv φ hφ K hK).apply_symm_apply a)

/-- Every element of K comes from this same inclusion. -/
theorem componentInclusion_range (φ : H →* Equiv.Perm (Fin 7))
    (hφ : Function.Injective φ) (K : Subgroup H)
    (hK : K.map φ = alternatingGroup (Fin 7)) :
    (componentInclusion φ hφ K hK).range = K := by
  ext k
  constructor
  · rintro ⟨a, rfl⟩
    exact ((componentEquiv φ hφ K hK).symm a).property
  · intro hk
    refine ⟨componentEquiv φ hφ K hK ⟨k, hk⟩, ?_⟩
    exact congrArg Subtype.val ((componentEquiv φ hφ K hK).symm_apply_apply ⟨k, hk⟩)

/-- The natural alternative supplies the requested linear equivalence. -/
theorem IsNatural.linearEquiv {ρ : Representation (ZMod 2) H E}
    {φ : H →* Equiv.Perm (Fin 7)} (h : IsNatural ρ φ) :
    ∃ e : BinaryPermutation.core (Fin 7) ≃ₗ[ZMod 2] E,
      ∀ g v, e (BinaryPermutation.coreRepresentation (Fin 7) (φ g) v) = ρ g (e v) := by
  obtain ⟨e⟩ := h
  exact ⟨e.toLinearEquiv, e.isIntertwining⟩

/-- The natural module has dimension six, as a consequence of the identification. -/
theorem IsNatural.finrank {ρ : Representation (ZMod 2) H E}
    {φ : H →* Equiv.Perm (Fin 7)} (h : IsNatural ρ φ) :
    Module.finrank (ZMod 2) E = 6 := by
  obtain ⟨e, _⟩ := h.linearEquiv
  rw [← e.finrank_eq, BinaryPermutation.finrank_core]
  decide

/-- The identification in particular gives the embedded core required by Sieve. -/
theorem IsNatural.hasNaturalSubmodule {ρ : Representation (ZMod 2) H E}
    {φ : H →* Equiv.Perm (Fin 7)} (h : IsNatural ρ φ) : HasNaturalSubmodule ρ φ := by
  obtain ⟨e, he⟩ := h.linearEquiv
  exact ⟨e.toLinearMap, e.injective, he⟩

/-- The precise specialized classification consequence retained as an earlier
input. It includes faithfulness, H-irreducibility and a nontrivial elementary
quadratic actor with the displacement bound. This consequence includes the
component-restriction/Clifford step; B.4.2 and B.4.5 alone are stated for
K-irreducible modules. It is not asserted to have been proved here. -/
def SmallQuadraticInput (φ : H →* Equiv.Perm (Fin 7)) (ι : A7 →* H) : Prop :=
  ∀ (F : Type*) [AddCommGroup F] [Module (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (σ : Representation (ZMod 2) H F), Function.Injective σ → IsIrreducible σ →
    ∀ A : Subgroup H, IsElementaryTwo A → IsQuadratic σ A →
      fixedCodim σ A ≤ 2 * rank A → SmallModuleAlternatives σ φ ι

/-- The four-space alternative really has binary dimension four. -/
theorem IsFour.finrank {ρ : Representation (ZMod 2) H E} {ι : A7 →* H}
    (h : IsFour ρ ι) : Module.finrank (ZMod 2) E = 4 := by
  obtain ⟨σ, _, ⟨e⟩⟩ := h
  rw [← e.toLinearEquiv.finrank_eq]
  exact Module.finrank_fin_fun (ZMod 2)

/-- The product with the contragredient really has binary dimension eight. -/
theorem IsFourPlusDual.finrank {ρ : Representation (ZMod 2) H E} {ι : A7 →* H}
    (h : IsFourPlusDual ρ ι) : Module.finrank (ZMod 2) E = 8 := by
  obtain ⟨σ, _, ⟨e⟩⟩ := h
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_prod, Subspace.dual_finrank_eq]
  norm_num [Four, Module.finrank_fin_fun]

/-- For a selected natural quotient its strong-FF exclusion is unconditional
and follows from the checked permutation-offender calculation. -/
theorem IsNatural.noStrong [FiniteDimensional (ZMod 2) E]
    {ρ : Representation (ZMod 2) H E} {φ : H →* Equiv.Perm (Fin 7)}
    (h : IsNatural ρ φ) (hφ : Function.Injective φ) : ¬ IsStrongFFModule ρ := by
  obtain ⟨j, hj, he⟩ := h.hasNaturalSubmodule
  exact no_strongOffender_of_embedded_core ρ φ hφ j hj he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
