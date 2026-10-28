module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryOffender.Basic

/-!
# Coordinate tests for fixed spaces of binary permutation sections

A full or core vector is fixed precisely when its coordinates are constant
on subgroup orbits. A vector modulo the constant line is fixed precisely when
each displacement is constant. This last condition retains the extra fixed
vectors that can appear on passing to the deleted or natural module.

The generator test follows by subgroup closure induction and applies to any
binary representation. These tests support the fixed-space calculations in
Aschbacher–Smith, *The Classification of Quasithin Groups*, B.3.2, pp. 83–84.
-/

public section

namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem mem_fixedSpace_iff (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (v : V) :
    v ∈ fixedSpace ρ A ↔ ∀ a ∈ A, ρ a v = v := by
  change (∀ a : A, ρ a.val v = v) ↔ _
  exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a.val a.property⟩

/-- A vector is fixed by a generated subgroup iff it is fixed by each generator. -/
theorem mem_fixedSpace_closure_iff (ρ : Representation (ZMod 2) G V)
    (s : Set G) (v : V) :
    v ∈ fixedSpace ρ (Subgroup.closure s) ↔ ∀ a ∈ s, ρ a v = v := by
  rw [mem_fixedSpace_iff]
  constructor
  · exact fun h a ha => h a (Subgroup.subset_closure ha)
  · intro h a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact h a ha
    | one => simp
    | mul a b _ _ ha hb => simp [map_mul, Module.End.mul_apply, ha, hb]
    | inv a _ ha =>
      calc
        ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := congrArg (ρ a⁻¹) ha.symm
        _ = v := by rw [← Module.End.mul_apply, ← map_mul]; simp

end Representation.BinaryOffender

namespace BinaryPermutation

open Representation.BinaryOffender

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
theorem mem_constants_iff (v : Full Ω) :
    v ∈ constants Ω ↔ ∃ c : ZMod 2, ∀ i, v i = c := by
  rw [constants, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by intro i; simp [allOne]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by ext i; simpa [allOne] using (hc i).symm⟩

omit [Fintype Ω] in
theorem mem_full_fixedSpace_iff (A : Subgroup (Equiv.Perm Ω)) (v : Full Ω) :
    v ∈ fixedSpace (representation Ω) A ↔ ∀ a ∈ A, ∀ i, v (a.symm i) = v i := by
  simp only [mem_fixedSpace_iff, funext_iff, representation_apply]

theorem mem_core_fixedSpace_iff (A : Subgroup (Equiv.Perm Ω)) (v : core Ω) :
    v ∈ fixedSpace (coreRepresentation Ω) A ↔
      ∀ a ∈ A, ∀ i, v.val (a.symm i) = v.val i := by
  simp only [mem_fixedSpace_iff, Subtype.ext_iff, coreRepresentation_apply,
    funext_iff, representation_apply]

omit [Fintype Ω] in
/-- Quotient fixed points allow a constant displacement, not necessarily zero. -/
theorem deleted_fixed_iff (a : Equiv.Perm Ω) (v : Full Ω) :
    deletedRepresentation Ω a ((constants Ω).mkQ v) = (constants Ω).mkQ v ↔
      ∃ c : ZMod 2, ∀ i, v (a.symm i) - v i = c := by
  rw [deletedRepresentation_mk]
  change (Submodule.Quotient.mk (representation Ω a v) : Deleted Ω) =
    Submodule.Quotient.mk v ↔ _
  rw [Submodule.Quotient.eq, mem_constants_iff]
  rfl

omit [Fintype Ω] in
theorem mem_deleted_fixedSpace_iff (A : Subgroup (Equiv.Perm Ω)) (v : Full Ω) :
    (constants Ω).mkQ v ∈ fixedSpace (deletedRepresentation Ω) A ↔
      ∀ a ∈ A, ∃ c : ZMod 2, ∀ i, v (a.symm i) - v i = c := by
  simp only [mem_fixedSpace_iff, deleted_fixed_iff]

theorem mem_natural_fixedSpace_iff (A : Subgroup (Equiv.Perm Ω)) (v : core Ω) :
    (⟨(constants Ω).mkQ v.val, ⟨v.val, v.property, rfl⟩⟩ : natural Ω) ∈
      fixedSpace (naturalRepresentation Ω) A ↔
      ∀ a ∈ A, ∃ c : ZMod 2, ∀ i, v.val (a.symm i) - v.val i = c := by
  simp only [mem_fixedSpace_iff, Subtype.ext_iff, naturalRepresentation_apply,
    deleted_fixed_iff]

omit [Fintype Ω] in
/-- A transposition fixes a full vector exactly when the two coordinates agree. -/
theorem swap_fixed_iff [DecidableEq Ω] (a b : Ω) (v : Full Ω) :
    representation Ω (Equiv.swap a b) v = v ↔ v a = v b := by
  constructor
  · intro h
    have h' := congrFun h a
    simpa using h'.symm
  · intro h
    ext i
    simp only [representation_apply, Equiv.symm_swap, Equiv.swap_apply_def]
    split_ifs with ha hb
    · simpa [ha] using h.symm
    · simpa [hb] using h
    · rfl

omit [Fintype Ω] in
/-- If a permutation has a fixed coordinate, its constant displacement must
vanish. Thus quotienting by constants creates no new fixed representatives. -/
theorem deleted_fixed_iff_of_fixed_point (a : Equiv.Perm Ω) (v : Full Ω)
    (i : Ω) (hi : a i = i) :
    deletedRepresentation Ω a ((constants Ω).mkQ v) = (constants Ω).mkQ v ↔
      representation Ω a v = v := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (deleted_fixed_iff a v).mp h
    have hi' : a.symm i = i := a.symm_apply_eq.mpr hi.symm
    have hc0 : c = 0 := by simpa [hi'] using (hc i).symm
    ext j
    exact sub_eq_zero.mp ((hc j).trans hc0)
  · intro h
    rw [deletedRepresentation_mk, h]

omit [Fintype Ω] in
/-- A transposition with a third coordinate has the same fixed-vector test
on the deleted module as on the full module. -/
theorem deleted_swap_fixed_iff [DecidableEq Ω] (a b k : Ω)
    (hka : k ≠ a) (hkb : k ≠ b) (v : Full Ω) :
    deletedRepresentation Ω (Equiv.swap a b) ((constants Ω).mkQ v) =
      (constants Ω).mkQ v ↔ v a = v b := by
  rw [deleted_fixed_iff_of_fixed_point _ _ k
    (Equiv.swap_apply_of_ne_of_ne hka hkb), swap_fixed_iff]

end BinaryPermutation
