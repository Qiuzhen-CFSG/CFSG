module

public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.Cubic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Recovering the marked plane geometry from rank-two displacements

Rank two is an explicit input. A pointwise-fixed plane alone would also admit
the wrong four-groups containing transvections. Rank-nullity identifies every
individual fixed space, and the displacement bound then proves isotropy.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
local notation "Bit" => ZMod 2

/-- Exact individual fixed planes and the displacement bound force isotropy.
This form directly accepts an original centralizer calculation. -/
public theorem isotropic_of_exact_fixed_plane
    (R : Subgroup (Sp Bit)) (W : Submodule Bit (Vector Bit))
    (hR : Nat.card R = 4) (hW : Module.finrank Bit W = 2)
    (hfixed : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W)
    (hmove : ∀ r ∈ R, ∀ v : Vector Bit, r • v-v ∈ W) :
    ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0 := by
  have hn : R ≠ ⊥ := by
    intro he
    have hh := Subgroup.card_eq_one.mpr he
    omega
  obtain ⟨r,hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  have hr1' : r.val ≠ 1 := fun hh => hr1 (Subtype.ext hh)
  let d := (toLinear r.val).toLinearMap-LinearMap.id
  have hker : LinearMap.ker d = W := by
    ext v
    change (r.val • v-v=0) ↔ v ∈ W
    rw [sub_eq_zero]
    exact hfixed r.val r.property hr1' v
  have hd : Module.finrank Bit (LinearMap.range d) = 2 := by
    have hh := d.finrank_range_add_finrank_ker
    rw [hker,hW] at hh
    have hV : Module.finrank Bit (Vector Bit) = 4 := by simp [Vector]
    omega
  have hrange : LinearMap.range d = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro v ⟨u,rfl⟩
      exact hmove r.val r.property u
    · exact hd.trans hW.symm
  intro x hx y hy
  rw [←hrange] at hx
  obtain ⟨v,rfl⟩ := hx
  change form Bit (r.val • v-v) y=0
  have hh := preserves_form r.val v y
  rw [(hfixed r.val r.property hr1' y).mpr hy] at hh
  rw [map_sub,LinearMap.sub_apply,hh,sub_self]

/-- The rank-two hypothesis recovers the exact individual fixed spaces and
the isotropy required by the native marked embedding. -/
public theorem geometry_of_rank_two
    (R : Subgroup (Sp Bit)) (W : Submodule Bit (Vector Bit))
    (hR : Nat.card R = 4) (hW : Module.finrank Bit W = 2)
    (hfix : ∀ r ∈ R, ∀ v ∈ W, r • v = v)
    (hmove : ∀ r ∈ R, ∀ v : Vector Bit, r • v-v ∈ W)
    (hrank : ∀ r ∈ R, r ≠ 1 → Module.finrank Bit
      (LinearMap.range ((toLinear r).toLinearMap-LinearMap.id)) = 2) :
    (∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0) ∧
    (∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W) := by
  have hdim : Module.finrank Bit (Vector Bit) = 4 := by simp [Vector]
  have hker (r : Sp Bit) (hr : r ∈ R) (hne : r ≠ 1) :
      LinearMap.ker ((toLinear r).toLinearMap-LinearMap.id) = W := by
    apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · intro v hv
      change r • v-v=0
      exact sub_eq_zero.mpr (hfix r hr v hv)
    · have hh := ((toLinear r).toLinearMap-LinearMap.id).finrank_range_add_finrank_ker
      rw [hrank r hr hne, hdim] at hh
      omega
  have hf : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W := by
    intro r hr hne v
    have hh : (r • v = v) ↔ v ∈ LinearMap.ker
        ((toLinear r).toLinearMap-LinearMap.id) := by
      change (r • v=v) ↔ r • v-v=0
      exact sub_eq_zero.symm
    rwa [hker r hr hne] at hh
  exact ⟨isotropic_of_exact_fixed_plane R W hR hW hf hmove, hf⟩

end Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
