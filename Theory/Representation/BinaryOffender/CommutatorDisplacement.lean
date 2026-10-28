module
public import Theory.Representation.BinaryOffender.NonStrongMovedSection

/-!
# Controlling component displacement through an actual quotient

When [K,A]=K, an invariant subspace containing [V,A] also contains [V,K].
In the action on its quotient, A lies in the kernel; normality of that
kernel and the group commutator identity put K in the same kernel.
All actors and maps are the original inclusions in K⋁A.

Source application: Aschbacher–Smith B.1.5 and13.7.15, pp.69,943–944.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- If [K,A]=K, containing every A-displacement makes an invariant space
contain every K-displacement. The quotient action carries the proof. -/
theorem subspaceCommutator_le_of_commutator_displacement
    {K A : Subgroup G} {W : Submodule (ZMod 2) V}
    (hgen : ⁅K,A⁆ = K) (hK : K ≤ subspaceStabilizer ρ W)
    (hA : A ≤ subspaceStabilizer ρ W) (hm : subspaceCommutator ρ ⊤ A ≤ W) :
    subspaceCommutator ρ ⊤ K ≤ W := by
  let H := K ⊔ A
  let I := invariantSubspace ρ H W (sup_le hK hA)
  let σ := I.quotientRepresentation
  have hAk : A.subgroupOf H ≤ σ.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      exact (Submodule.Quotient.eq W).mpr
        (hm (Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩))
  have hg : ⁅K.subgroupOf H,A.subgroupOf H⁆ = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),hgen]
  have hKk : K.subgroupOf H ≤ σ.ker := by
    rw [← hg]
    exact (commutator_mono le_rfl hAk).trans (commutator_le_right _ _)
  apply Submodule.span_le.mpr
  rintro _ ⟨k,hk,v,_,rfl⟩
  exact (Submodule.Quotient.eq W).mp
    (LinearMap.congr_fun (hKk (show (⟨k,(show K ≤ H from le_sup_left) hk⟩ : H) ∈
      K.subgroupOf H from hk)) (W.mkQ v))
end Representation.BinaryOffender
