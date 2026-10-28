module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction

/-!
# Maximal intersections of conjugate fixed spaces

Commuting distinct cyclic actors have fixed spaces spanning the ambient
space, so their intersection has the smallest possible dimension. A maximum
chosen among noncommuting pairs is consequently a maximum among all distinct
fixed-space pairs. The actual pointwise fixer is used for the local quotient.

These are deductions from the regular cyclic input for Aschbacher–Smith
E.6.24, printed p.255. They earn the maximal-intersection setup without
assuming that the ambient orbit of fixed spaces is TI.
-/

public section

open Module Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.RegularCyclicNormalClosure
namespace FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A W)

/-- Fixed spaces follow the actual conjugation map. -/
theorem fixedSpace_map_conj (C : Subgroup A) (a : A) :
    fixedSpace ρ (C.map (MulAut.conj a).toMonoidHom) =
      (fixedSpace ρ C).map (ρ a) := by
  apply le_antisymm
  · intro v hv
    refine ⟨ρ a⁻¹ v, ?_, ?_⟩
    · intro c
      have hh := hv ⟨a * (c : A) * a⁻¹, c, c.property, rfl⟩
      change ρ (a * (c : A) * a⁻¹) v = v at hh
      have hh' := congrArg (ρ a⁻¹) hh
      change ρ (c : A) (ρ a⁻¹ v) = ρ a⁻¹ v
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] using hh'
    · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
  · rintro _ ⟨v, hv, rfl⟩ b
    obtain ⟨c, hc, he⟩ := b.property
    change ρ (b : A) (ρ a v) = ρ a v
    rw [← he]
    change ρ (a * c * a⁻¹) (ρ a v) = ρ a v
    calc
      _ = ρ a (ρ c v) := by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      _ = ρ a v := congrArg (ρ a) (hv ⟨c, hc⟩)

/-- The literal pointwise fixer, without an implicit action instance on W. -/
@[expose] def pointwiseFixer (F : Submodule (ZMod 2) W) : Subgroup A where
  carrier := {a | ∀ v ∈ F, ρ a v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb v hv
    simp only [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have he := congrArg (ρ a⁻¹) (ha v hv)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using he.symm

@[simp] theorem mem_pointwiseFixer (F : Submodule (ZMod 2) W) (a : A) :
    a ∈ pointwiseFixer ρ F ↔ ∀ v ∈ F, ρ a v = v := Iff.rfl

/-- Containment in the pointwise fixer is the fixed-space containment. -/
theorem le_pointwiseFixer_iff (C : Subgroup A) (F : Submodule (ZMod 2) W) :
    C ≤ pointwiseFixer ρ F ↔ F ≤ fixedSpace ρ C := by
  constructor
  · intro h v hv c
    exact h c.property v hv
  · intro h c hc v hv
    exact h hv ⟨c, hc⟩

end FactorConstruction
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- Commuting distinct actor conjugates have fixed spaces whose sum is W. -/
theorem Input.fixed_sup_conjugate_eq_top_of_commuting (h : Input ρ C) (a : A)
    (hne : C.map (MulAut.conj a).toMonoidHom ≠ C)
    (hcomm : ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    fixedSpace ρ C ⊔ (fixedSpace ρ C).map (ρ a) = ⊤ := by
  have hcross := h.cross_fixed_of_commuting_conjugate a hne hcomm
  have hS : displacementSpan ρ C ⊤ ≤
      fixedSpace ρ (C.map (MulAut.conj a).toMonoidHom) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, v, _, rfl⟩ d
    have he := hcross c hc (ρ d v - v)
      (Submodule.subset_span ⟨d, d.property, v, Submodule.mem_top, rfl⟩)
    rw [map_sub] at he ⊢
    have hec : ρ (d : A) (ρ c v) = ρ c (ρ d v) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      rw [(hcomm c hc d d.property).eq]
    change ρ (d : A) (ρ c v) - ρ (d : A) v = ρ c v - v
    rw [hec]
    have he' := sub_eq_sub_iff_add_eq_add.mp he
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using he'
  rw [← fixedSpace_map_conj]
  exact top_unique (h.split.sup_eq_top ▸ sup_le_sup_left hS _)

/-- Commuting distinct pairs attain the minimum intersection dimension. -/
theorem Input.fixed_inf_finrank_of_commuting (h : Input ρ C) (a : A)
    (hne : C.map (MulAut.conj a).toMonoidHom ≠ C)
    (hcomm : ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)) +
      2 * finrank (ZMod 2) (displacementSpan ρ C ⊤) = finrank (ZMod 2) W := by
  have hr := (fixedSpace ρ C).finrank_sup_add_finrank_inf_eq
    ((fixedSpace ρ C).map (ρ a))
  rw [h.fixed_sup_conjugate_eq_top_of_commuting a hne hcomm, finrank_top] at hr
  have he := (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective
    (fixedSpace ρ C)).finrank_eq
  have hs := Submodule.finrank_add_eq_of_isCompl h.split
  omega

/-- The dimension inequality for any two conjugate fixed spaces. -/
theorem Input.le_fixed_inf_finrank (h : Input ρ C) (a : A) :
    finrank (ZMod 2) W ≤
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)) +
        2 * finrank (ZMod 2) (displacementSpan ρ C ⊤) := by
  have hr := (fixedSpace ρ C).finrank_sup_add_finrank_inf_eq
    ((fixedSpace ρ C).map (ρ a))
  have hb := (fixedSpace ρ C ⊔ (fixedSpace ρ C).map (ρ a)).finrank_le
  have he := (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective
    (fixedSpace ρ C)).finrank_eq
  have hs := Submodule.finrank_add_eq_of_isCompl h.split
  omega

/-- A noncommuting pair maximizing its fixed-space intersection is also
maximal among all distinct pairs based at the original fixed space. -/
theorem Input.exists_maximal_noncommuting [Finite A] (h : Input ρ C)
    (hex : ∃ a : A, ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    ∃ a : A,
      (¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) ∧
      (fixedSpace ρ C).map (ρ a) ≠ fixedSpace ρ C ∧
      ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
        finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤
          finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a)) := by
  classical
  let := Fintype.ofFinite A
  let := h.cyclic
  let s := Finset.univ.filter fun a : A =>
    ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hex
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image
    (fun a => finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ a))) hs
  have hnc := (Finset.mem_filter.mp ha).2
  refine ⟨a, hnc, ?_, ?_⟩
  · intro he
    apply hnc
    rw [h.normal_in_stabilizer a he]
    intro c hc d hd
    exact (Commute.all (⟨c, hc⟩ : C) ⟨d, hd⟩).map C.subtype
  · intro b hb
    by_cases hc : ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj b).toMonoidHom, Commute c d
    · have hne : C.map (MulAut.conj b).toMonoidHom ≠ C := by
        intro he
        exact hb ((fixedSpace_map_conj ρ C b).symm.trans (congrArg (fixedSpace ρ) he))
      have hh := h.fixed_inf_finrank_of_commuting b hne hc
      have hh' := h.le_fixed_inf_finrank a
      omega
    · exact hmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)

end Representation.RegularCyclicNormalClosure
