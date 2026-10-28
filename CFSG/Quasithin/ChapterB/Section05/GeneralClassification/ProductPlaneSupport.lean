module
public import Theory.Representation.BinaryOffender.MinimalPlane
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorPermutation

/-!
# Localizing a minimal plane offender in the B.5 product alternatives

In the two-factor alternative the prescribed spaces intersect only in the
global fixed space. Minimality therefore makes at least one quotient summand
fixed. In the hyperplane alternative the two actual moved spaces are disjoint,
so at least one is fixed already before taking a quotient. These conclusions
retain the literal module spaces of the adequate B.5 theorem; they do not
exclude products whose factors are permuted by an ambient group.

Source: Aschbacher–Smith B.5.6(3),(5) and13.7.15, printed pp.105,943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A minimal plane offender fixes one of the two literal quotient summands. -/
theorem SourceTwoFactorCase.minimal_plane_support (c : SourceTwoFactorCase ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) :
    subspaceCommutator ρ c.firstSpace.toSubmodule A ≤ ρ.invariants ∨
      subspaceCommutator ρ c.secondSpace.toSubmodule A ≤ ρ.invariants := by
  apply hA.centralizes_one_quotient ρ hd
  · exact le_subspaceStabilizer ρ _ (fun a _ _ hv => c.firstSpace.apply_mem_toSubmodule a hv)
  · exact le_subspaceStabilizer ρ _ (fun a _ _ hv => c.secondSpace.apply_mem_toSubmodule a hv)
  · intro v hv
    apply (Submodule.Quotient.mk_eq_zero ρ.invariants).mp
    exact Submodule.disjoint_def.mp c.decomposition.disjoint _
      ⟨v,hv.1,rfl⟩ ⟨v,hv.2,rfl⟩

/-- A minimal plane offender fixes one of the two original moved summands. -/
theorem HyperplaneCase.minimal_plane_support (c : HyperplaneCase ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) :
    moved ρ c.first ≤ fixedSpace ρ A ∨ moved ρ c.second ≤ fixedSpace ρ A := by
  let : c.first.Normal := c.product.swap.second_normal
  let : c.second.Normal := c.product.second_normal
  apply hA.fixes_one_of_disjoint ρ hd _ _ _ _ c.disjoint
  · exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp)) (by rw [normalizer_eq_top]; exact le_top)
  · exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp)) (by rw [normalizer_eq_top]; exact le_top)
end CFSG.Quasithin.ChapterB.SourceInduction
