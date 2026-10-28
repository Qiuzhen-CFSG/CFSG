module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# Simple two-core quotients in solvable-kernel images

A perfect subnormal subgroup with simple two-core quotient has the same
quotient in every surjective image with solvable kernel and trivial ambient
two-core. Solvability bounds the restricted kernel by the intrinsic two-core;
subnormality kills that core in the target. The resulting isomorphism retains
the original subgroup map.

Source application: Aschbacher--Smith 14.3.31, printed p.1003, comparing the
faithful component in the orbit-action and prime-to-three quotients.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- The intrinsic simple quotient is the actual image in a two-core-free target. -/
@[expose] noncomputable def IsSubnormal.simpleCoreImageEquiv
    (C : Subgroup G) (hC : C.IsSubnormal) [Group.IsPerfect C]
    [IsSimpleGroup (C ⧸ pCore 2 C)]
    (f : G →* D) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hcore : pCore 2 D = ⊥) : (C ⧸ pCore 2 C) ≃* C.map f := by
  let r := f.subgroupMap C
  let : Group.IsSolvable r.ker := by
    rw [ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := C.subtype.subgroupComap f.ker)
      (fun x y h => Subtype.ext (C.subtype_injective
        (congrArg (fun z : f.ker => (z : G)) h)))
  have hc : pCore 2 (C.map f) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (hC.map hf),hcore]
    exact (map f C).ker_subtype
  exact (PerfectCoreTwoExtension.solvableKernelQuotientEquiv r (f.subgroupMap_surjective C)).trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

/-- The image identification preserves the literal quotient representatives. -/
theorem IsSubnormal.simpleCoreImageEquiv_mk
    (C : Subgroup G) (hC : C.IsSubnormal) [Group.IsPerfect C]
    [IsSimpleGroup (C ⧸ pCore 2 C)]
    (f : G →* D) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hcore : pCore 2 D = ⊥) (c : C) :
    hC.simpleCoreImageEquiv C f hf hcore (QuotientGroup.mk' (pCore 2 C) c) =
      f.subgroupMap C c := rfl
end Subgroup
