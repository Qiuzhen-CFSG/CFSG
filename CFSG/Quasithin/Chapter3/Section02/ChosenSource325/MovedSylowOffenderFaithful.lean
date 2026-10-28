module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Fitting.PrimeSubgroups

/-!
# Faithfulness of the common actor on moved constituents

A constituent's pointwise kernel, computed inside its setwise stabilizer,
is normal there. The component dichotomy makes it centralize a normal
quasisimple component acting nontrivially on that constituent. When the
component is F* and the ambient two-core is trivial, this kernel contains
no nontrivial two-subgroup: the centralizer of F* is normal abelian and
its two-subgroups lie in O₂.

Thus the same elementary actor retains its rank on each constituent.
Neither the component nor its representation is assumed centerless.
The actual application is in `SeedAlternativesMovedActor`.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.3.5(2), printed pp.195--196, and the component dichotomy of A.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- A pointwise kernel on a noncentral constituent centralizes the normal
quasisimple component. No faithfulness or centerlessness of the component's
representation is assumed. -/
theorem subspaceKernel_le_component_centralizer
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (I : Submodule (ZMod 2) W) (hKI : K ≤ subspaceStabilizer ρ I)
    (hn : ¬ I ≤ fixedSpace ρ K) (A : Subgroup H) :
    subspaceKernel ρ I A ≤ centralizer (K : Set H) := by
  let S := subspaceStabilizer ρ I
  let X := K.subgroupOf S
  let τ := stabilizerRepresentation ρ I
  let N := τ.asGroupHom.ker
  let : IsQuasisimple X := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKI).symm
  have hX : IsComponent S X := ⟨(inferInstance : X.Normal).isSubnormal,inferInstance⟩
  have hXN : ¬ X ≤ N := by
    intro h
    apply hn
    intro v hv k
    have he := h (show (⟨k,hKI k.property⟩ : S) ∈ X from k.property)
    have hev := congrArg (fun q : (Module.End (ZMod 2) I)ˣ => (q.val ⟨v,hv⟩ : W)) he
    exact hev
  have hNX : N ≤ centralizer (X : Set S) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp ((hX.normal_dichotomy N).resolve_left hXN))
  have hS : subspaceKernel ρ I A ≤ S := by
    apply le_subspaceStabilizer
    intro a ha v hv
    rwa [ha.2 v hv]
  intro a ha k hk
  have haN : (⟨a,hS ha⟩ : S) ∈ N := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact Subtype.ext (ha.2 v v.property)
  exact congrArg Subtype.val (hNX haN ⟨k,hKI hk⟩ hk)

/-- Every elementary actor is faithful on each noncentral invariant summand
when F* is quasisimple and the ambient two-core is trivial. -/
theorem subspaceKernel_eq_bot_of_quasisimple_fitting [Finite H]
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hF : generalizedFitting H = K) (hcore : pCore 2 H = ⊥)
    (I : Submodule (ZMod 2) W) (hKI : K ≤ subspaceStabilizer ρ I)
    (hn : ¬ I ≤ fixedSpace ρ K) (A : Subgroup H) (hA : IsPGroup 2 A) :
    subspaceKernel ρ I A = ⊥ := by
  let C := centralizer (K : Set H)
  have hCK : C ≤ K := by
    simpa only [hF] using centralizer_generalizedFitting_le H
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    (show C ≤ centralizer (C : Set H) from (centralizer_le hCK))
  let : CommGroup C := IsMulCommutative.instCommGroup
  have hCF : C ≤ fittingSubgroup H := le_sSup ⟨inferInstance,inferInstance⟩
  have hKC : subspaceKernel ρ I A ≤ C :=
    subspaceKernel_le_component_centralizer ρ K I hKI hn A
  have hp : IsPGroup 2 (subspaceKernel ρ I A) :=
    hA.of_injective (inclusion (subspaceKernel_le ρ I A)) (inclusion_injective _)
  have he := hp.le_pCore_of_le_fitting (hKC.trans hCF)
  exact le_bot_iff.mp (he.trans hcore.le)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
