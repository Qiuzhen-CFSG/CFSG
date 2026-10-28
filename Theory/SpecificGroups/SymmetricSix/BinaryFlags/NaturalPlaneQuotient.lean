module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneChief
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneChief
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SubspaceQuotient

/-!
# Irreducibility above a fully moved natural seed plane

The canonical plane in the binary six-letter natural module is Lagrangian.
If an actor moves that whole plane, invariance of the symplectic pairing
shows that a fixed vector modulo the plane already lies in the plane.
A binary plane with no nonzero fixed vector is irreducible, so every
invariant subspace above the seed is the seed or the whole module.

This extension intentionally uses `import all NaturalPlaneChief` to reuse
its private Lagrangian calculation without changing that module's boundary.
The source consumer transports the result through the actual UH/V₁ action.
Source: Aschbacher--Smith, Lemma 13.8.33, printed p.966, last paragraph.
-/

public section
open BinaryPermutation Subgroup Module Representation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneQuotient
open NaturalGeometry NaturalPairing Representation.BinaryOffender

/-- Full movement of the Lagrangian plane excludes fixed vectors on its quotient. -/
theorem mem_plane_of_fixed_mod_plane (A : Subgroup S)
    (hm : subspaceCommutator (naturalRepresentation Ω) canonicalPlane A = canonicalPlane)
    (v : V) (hv : ∀ a ∈ A, naturalRepresentation Ω a v - v ∈ canonicalPlane) :
    v ∈ canonicalPlane := by
  have hp : canonicalPlane ≤ LinearMap.ker (form.flip v) := by
    rw [← hm]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, w, hw, rfl⟩
    change form (naturalRepresentation Ω a w - w) v = 0
    have hz : form w (naturalRepresentation Ω a⁻¹ v - v) = 0 := by
      have ht : naturalRepresentation Ω a⁻¹ v - v ∈ form.orthogonal canonicalPlane :=
        NaturalPlaneChief.plane_perp.symm ▸ hv a⁻¹ (A.inv_mem ha)
      exact ht w hw
    have he := form_invariant a w (naturalRepresentation Ω a⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at he
    rw [map_sub] at hz
    rw [map_sub, LinearMap.sub_apply, he]
    exact hz
  rw [← NaturalPlaneChief.plane_perp]
  intro w hw
  exact hp hw

private theorem binary_plane_irreducible_of_no_fixed {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hd : finrank (ZMod 2) W = 2)
    (hf : ∀ w, (∀ a, ρ a w = w) → w = 0) : IsIrreducible ρ := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro U
  by_cases hb : U = ⊥
  · exact Or.inl hb
  by_cases ht : U = ⊤
  · exact Or.inr ht
  exfalso
  have hb' : U.toSubmodule ≠ ⊥ := fun h => hb (Subrepresentation.toSubmodule_injective h)
  have ht' : U.toSubmodule ≠ ⊤ := fun h => ht (Subrepresentation.toSubmodule_injective h)
  have hdU : finrank (ZMod 2) U.toSubmodule = 1 := by
    have hl := Submodule.finrank_lt ht'
    have hp : finrank (ZMod 2) U.toSubmodule ≠ 0 :=
      fun hz => hb' (Submodule.finrank_eq_zero.mp hz)
    rw [hd] at hl
    omega
  have : Nontrivial U.toSubmodule := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : U.toSubmodule)
  apply hw
  apply Subtype.ext
  change (w : W) = 0
  apply hf
  intro a
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdU
    (U.toRepresentation a)
  have hi := (LinearMap.GeneralLinearGroup.toLinearEquiv
    (U.toRepresentation.asGroupHom a)).injective
  fin_cases c
  · have hz : U.toRepresentation a w = U.toRepresentation a 0 := by
      rw [hc]
      change (0 : ZMod 2) • w = (0 : ZMod 2) • 0
      simp only [zero_smul]
    exact (hw (hi hz)).elim
  · exact congrArg Subtype.val (show U.toRepresentation a w = w by rw [hc]; change (1 : ZMod 2) • w = w; exact one_smul _ w)

variable {A : Type*} [Group A] (f : A →* S)
  (hi : ∀ a, canonicalPlane.map (naturalRepresentation Ω (f a)) = canonicalPlane)

/-- The invariant plane retains the given actor homomorphism. -/
@[expose] def plane : Subrepresentation ((naturalRepresentation Ω).comp f) where
  toSubmodule := canonicalPlane
  apply_mem_toSubmodule a _v hv := hi a ▸ Submodule.mem_map_of_mem hv

/-- The literal quotient of the marked natural module is irreducible if the
actor moves the whole seed plane. -/
theorem quotient_irreducible
    (hm : subspaceCommutator (naturalRepresentation Ω) canonicalPlane f.range = canonicalPlane) :
    IsIrreducible (plane f hi).quotientRepresentation := by
  apply binary_plane_irreducible_of_no_fixed
  · have h := canonicalPlane.finrank_quotient_add_finrank
    rw [canonicalPlane_finrank, finrank_natural_even (Fin 6) (by decide), Fintype.card_fin] at h
    change finrank (ZMod 2) (V ⧸ canonicalPlane) = 2
    omega
  · intro w
    induction w using Submodule.Quotient.induction_on with
    | H w =>
      intro hw
      apply (Submodule.Quotient.mk_eq_zero canonicalPlane).mpr
      apply mem_plane_of_fixed_mod_plane f.range hm
      rintro _ ⟨a, rfl⟩
      exact (Submodule.Quotient.eq canonicalPlane).mp (hw a)

include hi in
/-- Every invariant subspace above the moved plane is the plane or the
whole natural module. This is the subgroup-kernel form of irreducibility. -/
theorem invariant_interval
    (hm : subspaceCommutator (naturalRepresentation Ω) canonicalPlane f.range = canonicalPlane)
    (D : Submodule (ZMod 2) V) (hPD : canonicalPlane ≤ D)
    (hD : ∀ a, D.map (naturalRepresentation Ω (f a)) = D) :
    D = canonicalPlane ∨ D = ⊤ := by
  let U : Subrepresentation ((naturalRepresentation Ω).comp f) := {
    toSubmodule := D
    apply_mem_toSubmodule a _v hv := hD a ▸ Submodule.mem_map_of_mem hv }
  let := quotient_irreducible f hi hm
  rcases Subrepresentation.le_or_sup_eq_top_of_irreducible_quotient (plane f hi) U with h | h
  · exact Or.inl (le_antisymm h hPD)
  · right
    change canonicalPlane ⊔ D = ⊤ at h
    rwa [sup_eq_right.mpr hPD] at h

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPlaneQuotient

