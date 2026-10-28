module

public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The marked subspace and its central quotient

The projection of `V/E` generates the first summand under the actual actor.
It therefore survives every nonzero quotient of that summand. In particular,
a subgroup fixing the marker cannot have zero fixed space on the natural
central quotient. No splitting of the original central extension is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction

variable {D L W X : Type*} [Group D] [Group L]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]

/-- The source marker, a Sylow subgroup and the subgroup whose normalizer
fixes the marker. In applications `J` is the actual image of `J(S_E)`.
That identification is a separate source-assembly obligation. -/
structure MarkedNormalizer (ρ : Representation (ZMod 2) D W) (J : Subgroup D) where
  sylow : Sylow 2 D
  subgroup_le_sylow : J ≤ (sylow : Subgroup D)
  marker : Submodule (ZMod 2) W
  marker_ne_bot : marker ≠ ⊥
  sylow_fixes : marker ≤ fixedSpace ρ (sylow : Subgroup D)
  orbit_span : Submodule.span (ZMod 2)
    {w | ∃ (g : D) (v : W), v ∈ marker ∧ ρ g v = w} = ⊤
  normalizer_fixes : ∀ g ∈ Subgroup.normalizer (J : Set D), ∀ v ∈ marker, ρ g v = v

/-- Coordinates on the literal central quotient, retaining both the group
isomorphism and the intertwining linear equivalence. -/
structure CentralQuotientCoordinates (ρ : Representation (ZMod 2) D W)
    (σ : Representation (ZMod 2) L X) where
  actor : D ≃* L
  coordinates : (W ⧸ ρ.invariants) ≃ₗ[ZMod 2] X
  intertwines : ∀ g v,
    coordinates (ρ.invariants.mkQ (ρ g v)) =
      σ (actor g) (coordinates (ρ.invariants.mkQ v))

/-- The marked subspace has a nonzero image in a nonzero central quotient.
Orbit generation supplies the missing condition even when the extension is
nonsplit and the marker contains globally fixed vectors. -/
theorem MarkedNormalizer.exists_nonzero_quotient_image [Nontrivial X]
    {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) L X}
    {J : Subgroup D} (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ σ) :
    ∃ v ∈ d.marker, c.coordinates (ρ.invariants.mkQ v) ≠ 0 := by
  classical
  by_contra! h
  let π := c.coordinates.toLinearMap.comp ρ.invariants.mkQ
  have hspan : Submodule.span (ZMod 2)
      {w | ∃ (g : D) (v : W), v ∈ d.marker ∧ ρ g v = w} ≤ π.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, v, hv, rfl⟩
    change c.coordinates (ρ.invariants.mkQ (ρ g v)) = 0
    rw [c.intertwines, h v hv, map_zero]
  rw [d.orbit_span] at hspan
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨v, hv⟩ := ρ.invariants.mkQ_surjective (c.coordinates.symm x)
  have hz : π v = 0 := hspan (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) W))
  exact hx (by simpa only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, hv,
    LinearEquiv.apply_symm_apply] using hz)

/-- The source normalizer containment is incompatible with a model subgroup
having zero fixed space. The normalizer comparison is on the actual image of
`J`, not on an unrelated model subgroup. -/
theorem MarkedNormalizer.model_fixedSpace_ne_bot [Nontrivial X]
    {ρ : Representation (ZMod 2) D W} {σ : Representation (ZMod 2) L X}
    {J : Subgroup D} (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ σ)
    (B : Subgroup L)
    (hB : B ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set L)) :
    fixedSpace σ B ≠ ⊥ := by
  obtain ⟨v, hv, hne⟩ := d.exists_nonzero_quotient_image c
  have hfix : c.coordinates (ρ.invariants.mkQ v) ∈ fixedSpace σ B := by
    intro b
    have hb : c.actor.symm b ∈ Subgroup.normalizer (J : Set D) := by
      have hbm := hB b.property
      rw [← J.map_normalizer_eq_of_bijective c.actor.bijective] at hbm
      obtain ⟨g, hg, hgb⟩ := hbm
      have he := congrArg c.actor.symm hgb
      change c.actor.symm (c.actor g) = c.actor.symm b at he
      rw [c.actor.symm_apply_apply] at he
      exact he ▸ hg
    have he := c.intertwines (c.actor.symm b) v
    rw [MulEquiv.apply_symm_apply, d.normalizer_fixes _ hb v hv] at he
    exact he.symm
  intro hz
  exact hne (by simpa only [hz, Submodule.mem_bot] using hfix)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
