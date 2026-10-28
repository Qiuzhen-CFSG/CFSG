module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.Basic

/-!
# Offender transport for odd binary permutation modules

Augmentation restricts to a surjection from the full fixed space to the scalar
field: in odd degree the all-one vector has augmentation one. Its kernel is
exactly the fixed space in the core. Rank-nullity therefore gives equal fixed
codimensions on the full module and the core. The equivariant identifications
of the core with the deleted and natural modules give the other two equalities.

The transport lemmas also show that equal codimensions for all subgroups
preserve best offenders, even when ambient dimensions differ.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.3.1(2) and B.3.2(4), printed pp. 83–84.
-/

public section

open Representation.BinaryOffender

namespace Representation.BinaryOffender.OddTransport
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)

/-- An equivariant linear equivalence identifies the two fixed spaces. -/
theorem fixedSpace_map_of_equivariant (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (A : Subgroup G) :
    (fixedSpace ρ A).map e.toLinearMap = fixedSpace σ A := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    apply (mem_fixedSpace_iff σ A _).mpr
    intro a ha
    exact (he a v).symm.trans (congrArg e ((mem_fixedSpace_iff ρ A v).mp hv a ha))
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    apply (mem_fixedSpace_iff ρ A _).mpr
    intro a ha
    apply e.injective
    simpa only [he, e.apply_symm_apply] using (mem_fixedSpace_iff σ A w).mp hw a ha

/-- Equivariantly isomorphic representations have equal fixed codimensions. -/
theorem fixedCodim_eq_of_equivariant [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W] (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) (A : Subgroup G) :
    fixedCodim ρ A = fixedCodim σ A := by
  have hf := e.finrank_map_eq (fixedSpace ρ A)
  rw [fixedSpace_map_of_equivariant ρ σ e he] at hf
  have hV := e.finrank_eq
  have hρ := fixedCodim_add_finrank ρ A
  have hσ := fixedCodim_add_finrank σ A
  omega

/-- Equal fixed codimensions preserve best offenders despite differing ambient dimensions. -/
theorem isBestOffender_iff_of_fixedCodim_eq [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W]
    (h : ∀ A, fixedCodim ρ A = fixedCodim σ A) (A : Subgroup G) :
    IsBestOffender ρ A ↔ IsBestOffender σ A := by
  have hw (B : Subgroup G) : weight ρ B ≤ weight ρ A ↔ weight σ B ≤ weight σ A := by
    have hρA := fixedCodim_add_finrank ρ A
    have hρB := fixedCodim_add_finrank ρ B
    have hσA := fixedCodim_add_finrank σ A
    have hσB := fixedCodim_add_finrank σ B
    have := h A
    have := h B
    unfold weight
    omega
  simp only [IsBestOffender, hw]
end Representation.BinaryOffender.OddTransport

namespace BinaryPermutation

open Representation.BinaryOffender.OddTransport
variable (Ω : Type*) [Fintype Ω]

/-- In odd degree, augmentation removes one dimension from the full fixed space. -/
theorem finrank_full_fixedSpace_odd (h : Odd (Fintype.card Ω))
    (A : Subgroup (Equiv.Perm Ω)) :
    Module.finrank (ZMod 2) (fixedSpace (representation Ω) A) =
      Module.finrank (ZMod 2) (fixedSpace (coreRepresentation Ω) A) + 1 := by
  let F := fixedSpace (representation Ω) A
  let f := (augmentation Ω).domRestrict F
  have hsum : augmentation Ω (allOne Ω) = 1 := by
    rw [augmentation_allOne, h.natCast_zmod_two]
  have hs : Function.Surjective f := by
    intro c
    refine ⟨⟨c • allOne Ω, ?_⟩, ?_⟩
    · rw [mem_fixedSpace_iff]
      intro a _
      simp
    · change augmentation Ω (c • allOne Ω) = c
      simp [hsum]
  let e : LinearMap.ker f ≃ₗ[ZMod 2] fixedSpace (coreRepresentation Ω) A :=
    { toFun := fun v => ⟨⟨v.val.val, v.property⟩,
        (mem_core_fixedSpace_iff A _).mpr
          ((mem_full_fixedSpace_iff A _).mp v.val.property)⟩
      invFun := fun v => ⟨⟨v.val.val,
        (mem_full_fixedSpace_iff A _).mpr
          ((mem_core_fixedSpace_iff A _).mp v.property)⟩, v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    e.finrank_eq] at hf
  simpa only [F, Nat.add_comm] using hf.symm

/-- The core and full modules have equal fixed codimensions in odd degree. -/
theorem fixedCodim_core_eq_full_odd (h : Odd (Fintype.card Ω))
    (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (coreRepresentation Ω) A = fixedCodim (representation Ω) A := by
  have hpos : 0 < Fintype.card Ω := h.pos
  let : Nonempty Ω := Fintype.card_pos_iff.mp hpos
  have hF := fixedCodim_add_finrank (representation Ω) A
  have hC := fixedCodim_add_finrank (coreRepresentation Ω) A
  rw [finrank_full, finrank_full_fixedSpace_odd Ω h] at hF
  rw [finrank_core] at hC
  omega

/-- The deleted and full modules have equal fixed codimensions in odd degree. -/
theorem fixedCodim_deleted_eq_full_odd (h : Odd (Fintype.card Ω))
    (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (deletedRepresentation Ω) A = fixedCodim (representation Ω) A := by
  have he := fixedCodim_eq_of_equivariant (coreRepresentation Ω) (deletedRepresentation Ω)
    (coreEquivDeleted Ω h) (fun _ _ => rfl) A
  exact he.symm.trans (fixedCodim_core_eq_full_odd Ω h A)

/-- The natural and full modules have equal fixed codimensions in odd degree. -/
theorem fixedCodim_natural_eq_full_odd (h : Odd (Fintype.card Ω))
    (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (naturalRepresentation Ω) A = fixedCodim (representation Ω) A := by
  have he := fixedCodim_eq_of_equivariant (coreRepresentation Ω) (naturalRepresentation Ω)
    (coreEquivNatural Ω h) (coreEquivNatural_equivariant Ω h) A
  exact he.symm.trans (fixedCodim_core_eq_full_odd Ω h A)
end BinaryPermutation
