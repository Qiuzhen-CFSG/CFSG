module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.SupportRigidity

/-!
# Displacement ranges of nonidentity regular cyclic actors

Every nonidentity element of the regular cyclic subgroup has the same fixed
space as the subgroup. Rank-nullity identifies its displacement range with
the whole moved space. This identity is preserved by the actual conjugation
map. It supplies both rank-two ranges used in the four-dimensional pair
argument for Aschbacher--Smith E.6.24, printed p.255.
-/

public section
open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- Every nonidentity regular cyclic actor has exactly the full moved range. -/
theorem Input.displacement_range_eq (h : Input ρ C) {c : A} (hc : c ∈ C) (hc1 : c ≠ 1) :
    (ρ c - LinearMap.id).range = displacementSpan ρ C ⊤ := by
  have hle : (ρ c - LinearMap.id).range ≤ displacementSpan ρ C ⊤ := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨c, hc, v, Submodule.mem_top, rfl⟩
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← fixedCodim_zpowers_eq_displacement_rank, fixedCodim, h.fixedSpace_zpowers hc hc1]
  exact (moved_finrank_eq_fixedCodim ρ h.split).symm

omit [FiniteDimensional (ZMod 2) W] in
/-- Displacement ranges follow the literal action on conjugating vectors. -/
theorem displacement_range_conjugate (ρ : Representation (ZMod 2) A W) (c a : A) :
    (ρ (a * c * a⁻¹) - LinearMap.id).range = ((ρ c - LinearMap.id).range).map (ρ a) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨ρ c (ρ a⁻¹ w) - ρ a⁻¹ w, ⟨ρ a⁻¹ w, rfl⟩, ?_⟩
    simp only [map_sub, LinearMap.sub_apply, LinearMap.id_apply, map_mul, Module.End.mul_apply]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨ρ a w, ?_⟩
    simp only [map_sub, LinearMap.sub_apply, LinearMap.id_apply, map_mul, Module.End.mul_apply]
    congr 1
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- A nonidentity member of a conjugate actor has that conjugate's moved range. -/
theorem Input.displacement_range_eq_conjugate (h : Input ρ C) (a : A) {d : A}
    (hd : d ∈ C.map (MulAut.conj a).toMonoidHom) (hd1 : d ≠ 1) :
    (ρ d - LinearMap.id).range = displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤ := by
  obtain ⟨c, hc, rfl⟩ := hd
  have hc1 : c ≠ 1 := by intro he; apply hd1; rw [he, map_one]
  change (ρ (a * c * a⁻¹) - LinearMap.id).range = _
  rw [displacement_range_conjugate, h.displacement_range_eq hc hc1,
    ← displacementSpan_conjugate, map_top_action]

end Representation.RegularCyclicNormalClosure
