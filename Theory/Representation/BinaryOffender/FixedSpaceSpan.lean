module

public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Spans of element fixed spaces

For a subgroup `A`, take the sum of the fixed spaces of its nonidentity
elements. Two such spaces already give a lower bound on that sum by the
dimension formula for a sum and intersection. Equivariant identifications
of both the acting group and the module preserve the sum and its quotient.

This is the construction denoted by `ξ_V(A)` in Aschbacher–Smith,
Definition H.10.1, printed p.392, and the dimension argument used in H.16.8,
printed p.405 (combined manuscript of 1 March 2004).
-/

@[expose] public section

namespace Representation.BinaryOffender

variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- The sum of `C_V(a)` over the nonidentity elements of `A`. -/
noncomputable def fixedSpaceSpan (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) : Submodule (ZMod 2) V :=
  ⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), fixedSpace ρ (Subgroup.zpowers a)

variable (ρ : Representation (ZMod 2) G V)

theorem fixedSpace_le_fixedSpaceSpan {A : Subgroup G} {a : G}
    (ha : a ∈ A) (hne : a ≠ 1) :
    fixedSpace ρ (Subgroup.zpowers a) ≤ fixedSpaceSpan ρ A :=
  le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le hne le_rfl))

theorem fixedSpaceSpan_le {A : Subgroup G} {U : Submodule (ZMod 2) V}
    (hU : ∀ a ∈ A, a ≠ 1 → fixedSpace ρ (Subgroup.zpowers a) ≤ U) :
    fixedSpaceSpan ρ A ≤ U :=
  iSup_le fun a => iSup_le fun ha => iSup_le fun hne => hU a ha hne

theorem fixedSpaceSpan_mono {A B : Subgroup G} (hAB : A ≤ B) :
    fixedSpaceSpan ρ A ≤ fixedSpaceSpan ρ B :=
  fixedSpaceSpan_le ρ fun _ ha hne => fixedSpace_le_fixedSpaceSpan ρ (hAB ha) hne

/-- Two element centralizers give a bound on the codimension of their span.
The hypothesis is a dimension inequality for the two individual spaces and
their intersection, rather than an assumption about the resulting span. -/
theorem fixedSpaceSpan_codim_le_of_pair [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (d : ℕ)
    (hd : Module.finrank (ZMod 2) V + Module.finrank (ZMod 2)
        ↥(fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers b)) ≤
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) +
        Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers b)) + d) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) ≤ d := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ (Subgroup.zpowers a)) (fixedSpace ρ (Subgroup.zpowers b))
  have hle := Submodule.finrank_mono (sup_le
    (fixedSpace_le_fixedSpaceSpan ρ ha ha1) (fixedSpace_le_fixedSpaceSpan ρ hb hb1))
  have hquot := (fixedSpaceSpan ρ A).finrank_quotient_add_finrank
  omega

/-- If every element centralizer lies in `U`, two of them of the required
dimensions identify the entire fixed-space span with `U`. -/
theorem fixedSpaceSpan_eq_of_pair [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (U : Submodule (ZMod 2) V)
    (hU : ∀ c ∈ A, c ≠ 1 → fixedSpace ρ (Subgroup.zpowers c) ≤ U)
    (hd : Module.finrank (ZMod 2) U + Module.finrank (ZMod 2)
        ↥(fixedSpace ρ (Subgroup.zpowers a) ⊓ fixedSpace ρ (Subgroup.zpowers b)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers a)) +
        Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers b))) :
    fixedSpaceSpan ρ A = U := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (fixedSpace ρ (Subgroup.zpowers a)) (fixedSpace ρ (Subgroup.zpowers b))
  have hle := Submodule.finrank_mono (sup_le
    (fixedSpace_le_fixedSpaceSpan ρ ha ha1) (fixedSpace_le_fixedSpaceSpan ρ hb hb1))
  have hUle := fixedSpaceSpan_le ρ hU
  have hleU := Submodule.finrank_mono hUle
  exact Submodule.eq_of_le_of_finrank_eq hUle (by omega)

variable (σ : Representation (ZMod 2) D W)

/-- An injective change of actors and an intertwining linear equivalence
transport the actual sum of fixed spaces. -/
theorem fixedSpaceSpan_map_equivariant (f : G →* D) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (A : Subgroup G) :
    (fixedSpaceSpan ρ A).map E.toLinearMap = fixedSpaceSpan σ (A.map f) := by
  simp only [fixedSpaceSpan, Submodule.map_iSup,
    fixedSpace_map_equivariant ρ σ f E hE, MonoidHom.map_zpowers]
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    have hfa : f a ≠ 1 := fun h => ha1 (hf (h.trans (map_one f).symm))
    exact le_iSup_of_le (f a) (le_iSup_of_le (Subgroup.mem_map_of_mem f ha)
      (le_iSup_of_le hfa le_rfl))
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    obtain ⟨a, ha, rfl⟩ := hb
    have ha1 : a ≠ 1 := fun h => hb1 (h ▸ map_one f)
    exact le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))

/-- In particular the codimension of the span is independent of the marking. -/
theorem fixedSpaceSpan_codim_map_equivariant (f : G →* D)
    (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) (A : Subgroup G) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpaceSpan ρ A) =
      Module.finrank (ZMod 2) (W ⧸ fixedSpaceSpan σ (A.map f)) :=
  (Submodule.Quotient.equiv _ _ E
    (fixedSpaceSpan_map_equivariant ρ σ f hf E hE A)).finrank_eq

end Representation.BinaryOffender
