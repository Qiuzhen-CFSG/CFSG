module
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.PCoreFrattiniTransport
/-!
# Solvable kernels preserve a simple two-core quotient

A perfect finite group whose two-core quotient is simple has solvable radical
exactly its two-core. Every solvable homomorphism kernel is therefore a
two-group, so a surjection preserves the literal quotient by the two-core.
The compatibility lemma identifies the induced map on original elements.

Source application: Aschbacher–Smith A.3.12 and 15.3.32(3), printed pp.47–48
and1133, on the smaller A₈ section of the containing component.
-/

public section
open Subgroup
namespace Theory.GroupTheory.PerfectCoreTwoExtension
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Group.IsPerfect G] [IsSimpleGroup (G ⧸ pCore 2 G)]
omit [Finite H] in
/-- Every solvable kernel lies in the original two-core. -/
theorem ker_isTwoGroup (f : G →* H) [Group.IsSolvable f.ker] :
    IsPGroup 2 f.ker := by
  have hk : f.ker ≤ pCore 2 G := by
    rw [← radical_eq_core]
    exact le_solvableRadical f.ker inferInstance inferInstance
  exact pCore_isPGroup.of_injective (inclusion hk) (inclusion_injective hk)
/-- The actual induced two-core quotient equivalence. -/
@[expose] noncomputable def solvableKernelQuotientEquiv (f : G →* H)
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    G ⧸ pCore 2 G ≃* H ⧸ pCore 2 H :=
  f.pCoreQuotientEquiv hf (ker_isTwoGroup f)
/-- The equivalence uses the original homomorphism and quotient maps. -/
@[simp] theorem solvableKernelQuotientEquiv_mk (f : G →* H)
    (hf : Function.Surjective f) [Group.IsSolvable f.ker] (g : G) :
    solvableKernelQuotientEquiv f hf (QuotientGroup.mk' (pCore 2 G) g) =
      QuotientGroup.mk' (pCore 2 H) (f g) := rfl
end Theory.GroupTheory.PerfectCoreTwoExtension
