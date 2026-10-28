module

public import Theory.GroupAction.TypedCosetGeometry.Residues.Quotient

/-!
# Normal cores of faithful homogeneous spaces and quotient cosets

A faithful transitive action has core-free point stabilizers. Pulling back
such a coset action along a surjection gives exactly the quotient kernel.
These facts identify the literal local point and line kernels in
Aschbacher–Smith I.5.4 and I.5.8, printed pp.420–421.
-/

public section
open Subgroup

theorem MulAction.stabilizer_normalCore_eq_bot_of_faithful {H X : Type*} [Group H] [MulAction H X]
    [MulAction.IsPretransitive H X] [FaithfulSMul H X] (x : X) :
    (MulAction.stabilizer H x).normalCore = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq H x y
  have h := hg a⁻¹
  change (a⁻¹ * g * (a⁻¹)⁻¹) • x = x at h
  have he := congrArg (a • ·) h
  simpa only [inv_inv, mul_smul, smul_inv_smul, one_smul] using he


theorem Subgroup.normalCore_eq_ker_of_map_core_free {H K : Type*} [Group H] [Group K]
    (P : Subgroup H) (f : H →* K) (hf : Function.Surjective f) (hk : f.ker ≤ P)
    (hmodel : (P.map f).normalCore = ⊥) : P.normalCore = f.ker := by
  have ht : (P.map f).normalCore.comap f = P.normalCore := by
    simpa only [inf_idem] using
      CosetGeometry.QuotientTransport.normalCore_inf_comap P P f hf (le_inf hk hk)
  rw [← ht, hmodel, MonoidHom.comap_bot]
