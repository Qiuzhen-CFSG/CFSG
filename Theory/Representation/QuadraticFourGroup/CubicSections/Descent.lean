module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient

/-!
# Descent of binary orbit sections through the two-core

The normal p-subgroup fixed-vector theorem kills the intrinsic two-core on
any irreducible binary representation. The literal quotient action therefore
transports along `TwoFactorModel.quotientEquiv` on the same vector space.
Surjectivity preserves both irreducibility and triviality.

This supplies the quotient descent used in GLS, volume 2, Theorem 25.14,
Steps 2–4. It applies to actual invariant subquotients and retains trivial
factors. It does not yet prove the order-three fixed-point assertion.
-/

@[expose] public section

namespace Representation.QuadraticFourGroup

section Inflation
variable {k G Q V W : Type*} [Field k] [Group G] [Group Q]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Surjective inflation reflects actual irreducible subquotients. -/
theorem IsIrreducibleSection.of_comp_surjective (π : G →* Q) (hπ : Function.Surjective π)
    {ρ : Representation k Q V} {σ : Representation k Q W}
    (hs : IsIrreducibleSection (ρ.comp π) (σ.comp π)) : IsIrreducibleSection ρ σ := by
  obtain ⟨hirr, U₀, N₀, ⟨e⟩⟩ := hs
  let U := inflationSubrepresentationOrderIso π hπ ρ U₀
  let N := inflationSubrepresentationOrderIso π hπ U.toRepresentation N₀
  exact ⟨(irreducible_comp_surjective_iff π hπ σ).mp hirr, U, N,
    ⟨inflationEquiv π hπ N.quotientRepresentation σ e⟩⟩

end Inflation

variable {E W : Type*} [Group E] [Finite E]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The intrinsic two-core kills every irreducible binary representation. -/
theorem twoCore_le_ker (σ : Representation (ZMod 2) E W) [σ.IsIrreducible] :
    pCore 2 E ≤ σ.ker :=
  normal_p_subgroup_le_ker σ (pCore 2 E) pCore_isPGroup

namespace TwoFactorModel

variable (M : TwoFactorModel E) (σ : Representation (ZMod 2) E W) [σ.IsIrreducible]

/-- The section action on the two concrete factors, on its original space. -/
noncomputable def sectionRepresentation :
    Representation (ZMod 2) (Factor M.n × Factor M.n) W :=
  (quotientOfLEKer σ (pCore 2 E) (twoCore_le_ker σ)).comp
    M.quotientEquiv.symm.toMonoidHom

@[simp] theorem sectionRepresentation_projection (g : E) :
    M.sectionRepresentation σ (M.projection g) = σ g := by
  simp only [sectionRepresentation, projection, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem sectionRepresentation_comp :
    (M.sectionRepresentation σ).comp M.projection = σ := by
  ext g w
  exact congrArg (fun f => f w) (M.sectionRepresentation_projection σ g)

theorem sectionRepresentation_irreducible : (M.sectionRepresentation σ).IsIrreducible := by
  apply (irreducible_comp_surjective_iff M.projection M.projection_surjective _).mp
  rw [sectionRepresentation_comp]
  infer_instance

theorem sectionRepresentation_isTrivial_iff :
    (M.sectionRepresentation σ).IsTrivial ↔ σ.IsTrivial := by
  constructor
  · intro h
    refine ⟨fun g => ?_⟩
    rw [← M.sectionRepresentation_projection σ g]
    exact h.out _
  · intro h
    refine ⟨fun g => ?_⟩
    obtain ⟨g, rfl⟩ := M.projection_surjective g
    rw [M.sectionRepresentation_projection σ g]
    exact h.out _

end TwoFactorModel

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Every actual irreducible section has a compatible irreducible descent. -/
theorem exists_sectionRepresentation (ρ : Representation (ZMod 2) G V)
    (E : Subgroup G) [Finite E] (M : TwoFactorModel E)
    (σ : Representation (ZMod 2) E W)
    (hs : IsIrreducibleSection (ρ.comp E.subtype) σ) :
    ∃ σbar : Representation (ZMod 2) (Factor M.n × Factor M.n) W,
      σbar.comp M.projection = σ ∧ σbar.IsIrreducible ∧
        (σbar.IsTrivial ↔ σ.IsTrivial) := by
  let := hs.1
  exact ⟨M.sectionRepresentation σ, M.sectionRepresentation_comp σ,
    M.sectionRepresentation_irreducible σ, M.sectionRepresentation_isTrivial_iff σ⟩

end Representation.QuadraticFourGroup

end
