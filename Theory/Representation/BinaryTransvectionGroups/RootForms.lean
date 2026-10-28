module

public import Theory.Representation.BinaryTransvectionGroups.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Linear forms of binary root groups

The forms defining the transvections with a fixed center form a subspace of
the dual.  A subspace of forms whose nonorthogonal centers have all the
corresponding root forms has an invariant annihilator.  This is the linear
algebra needed to use global irreducibility in a recognition argument.

Source motivation: Aschbacher--Smith, G.3.1, printed pp.337--338.  The invariant
annihilator argument does not assert that a chosen boundary root moves the
fixed space of a local subgroup.
-/

@[expose] public section

namespace BinaryTransvectionGroups
open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem transvection_zero (x : V) : transvection x 0 (by simp) = 1 := by
  ext v
  simp [transvection]

theorem transvection_add (x : V) (f g : Module.Dual (ZMod 2) V)
    (hf : f x = 0) (hg : g x = 0) :
    transvection x (f + g) (by simp [hf, hg]) =
      transvection x f hf * transvection x g hg := by
  ext v
  simp [transvection, hf, add_smul]
  abel

/-- The actual forms occurring in the root group at `x`. -/
def rootForms (G : Subgroup (GL V)) (x : V) : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) where
  carrier := {f | ∃ hf : f x = 0, transvection x f hf ∈ G}
  zero_mem' := ⟨by simp, by rw [transvection_zero]; exact G.one_mem⟩
  add_mem' := by
    rintro f g ⟨hf, htf⟩ ⟨hg, htg⟩
    exact ⟨by simp [hf, hg], by
      rw [transvection_add x f g hf hg]
      exact G.mul_mem htf htg⟩
  smul_mem' := by
    intro a f hf
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · exact ⟨by simp, by simp [transvection_zero]⟩
    · simpa using hf

theorem mem_rootForms {G : Subgroup (GL V)} {x : V}
    {f : Module.Dual (ZMod 2) V} (hf : f x = 0) :
    f ∈ rootForms G x ↔ transvection x f hf ∈ G := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · exact fun h => ⟨hf, h⟩

theorem rootForms_apply_center {G : Subgroup (GL V)} {x : V}
    {f : Module.Dual (ZMod 2) V} (hf : f ∈ rootForms G x) : f x = 0 := hf.1

theorem mem_line_annihilator (x : V) (f : Module.Dual (ZMod 2) V) :
    f ∈ (centerLine x).dualAnnihilator ↔ f x = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · exact fun h => h x (Submodule.mem_span_singleton_self x)
  · intro h v hv
    rcases (mem_centerLine_iff x v).mp hv with rfl | rfl
    · exact f.map_zero
    · exact h

theorem rootForms_le_annihilator (G : Subgroup (GL V)) (x : V) :
    rootForms G x ≤ (centerLine x).dualAnnihilator :=
  fun _ hf => (mem_line_annihilator _ _).mpr hf.1

theorem transvection_mem_rootGroup_of_form {G : Subgroup (GL V)} {x : V}
    {f : Module.Dual (ZMod 2) V} (hf : f ∈ rootForms G x) :
    transvection x f hf.1 ∈ rootGroup G x := by
  exact ⟨hf.2, transvection_mem (Submodule.mem_span_singleton_self x)
    (by
      intro v hv
      exact (Submodule.mem_dualAnnihilator f).mp (rootForms_le_annihilator G x hf) v hv)⟩

/-- A root-form envelope may have an annihilator.  This predicate imposes no
irreducibility and does not assert that the envelope is the whole dual. -/
def IsRootFormEnvelope (G : Subgroup (GL V)) (Δ : Set V)
    (E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)) : Prop :=
  E ≠ ⊥ ∧ ∀ x ∈ Δ, x ∈ E.dualCoannihilator ∨
    rootForms G x = E ⊓ (centerLine x).dualAnnihilator

/-- A local seed for propagating a root-form envelope.  All its nonzero
vectors are actual centers, and its root forms are hyperplanes in the same
dual subspace.  Separation excludes a local common fixed vector. -/
structure IsRootFormSeed (G : Subgroup (GL V)) (Δ : Set V)
    (W : Submodule (ZMod 2) V)
    (E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)) : Prop where
  dimension_ge_three : 3 ≤ Module.finrank (ZMod 2) W
  points : ∀ x ∈ W, x ≠ 0 → x ∈ Δ
  separates : Disjoint W E.dualCoannihilator
  forms : ∀ x ∈ W, x ≠ 0 → rootForms G x = E ⊓ (centerLine x).dualAnnihilator

/-- Every root preserves the annihilator of a root-form envelope: its center
lies in the annihilator, or its defining form vanishes on it. -/
theorem rootGroup_le_parabolic_envelope {G : Subgroup (GL V)} {Δ : Set V}
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}
    (he : IsRootFormEnvelope G Δ E) {x : V} (hx : x ∈ Δ) (hx0 : x ≠ 0) :
    rootGroup G x ≤ parabolic E.dualCoannihilator := by
  have hs (a : GL V) (ha : a ∈ rootGroup G x) {v : V}
      (hv : v ∈ E.dualCoannihilator) : a v ∈ E.dualCoannihilator := by
    obtain ⟨haG, f, hf, rfl⟩ := (mem_rootGroup_iff hx0).mp ha
    change v + f v • x ∈ E.dualCoannihilator
    rcases he.2 x hx with hxc | hforms
    · exact E.dualCoannihilator.add_mem hv (E.dualCoannihilator.smul_mem _ hxc)
    · have hfE : f ∈ E := by
        have hfm : f ∈ rootForms G x := (mem_rootForms hf).mpr haG
        rw [hforms] at hfm
        exact hfm.1
      rw [(Submodule.mem_dualCoannihilator v).mp hv f hfE, zero_smul, add_zero]
      exact hv
  intro a ha v
  constructor
  · intro hv
    simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
      hs a⁻¹ ((rootGroup G x).inv_mem ha) hv
  · exact hs a ha

theorem generated_le_parabolic_envelope {G : Subgroup (GL V)} {Δ : Set V}
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}
    (he : IsRootFormEnvelope G Δ E) (hnz : ∀ x ∈ Δ, x ≠ 0) :
    generated G Δ ≤ parabolic E.dualCoannihilator :=
  iSup_le fun x => iSup_le fun hx => rootGroup_le_parabolic_envelope he hx (hnz x hx)

end BinaryTransvectionGroups
