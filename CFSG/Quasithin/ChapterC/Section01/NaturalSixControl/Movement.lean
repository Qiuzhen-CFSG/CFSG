module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.FixedGeometry
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# Generation of the actual natural module by the two-residual

An even permutation moves one duad vector, giving a nonzero displacement.
The displacement span is invariant, and A₆ is transitive on nonzero vectors,
so that span is the whole four-dimensional natural module. Equivariant
coordinates and the established ambient commutator comparison transfer the
conclusion to the original normal elementary subgroup.

Source: Aschbacher--Smith C.1.37, printed pp.141--143; the natural S₆ case
of the module conditions used with B.2.19 and B.2.20.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Representation.BinaryOffender
universe u
namespace Model

/-- The even permutations generate the whole natural module by displacements. -/
theorem moved_alternating_eq_top : subspaceCommutator rho ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
  let W := subspaceCommutator rho ⊤ (alternatingGroup (Fin 6))
  obtain ⟨g, hg⟩ := NaturalTransport.transitive_nonzero (pairVector 0 1)
    (pairVector 4 5) pairVector01_ne_zero pairVector45_ne_zero
  let z := rho g.val (pairVector 0 1) - pairVector 0 1
  have hz : z ∈ W := Submodule.subset_span
    ⟨g.val,g.property,pairVector 0 1,Submodule.mem_top,rfl⟩
  have hz0 : z ≠ 0 := by
    intro he
    have hp := (pairVector_eq_iff (by decide : (4 : Fin 6) ≠ 5)
      (by decide : (0 : Fin 6) ≠ 1)).mp ((hg.symm.trans (sub_eq_zero.mp he)))
    exact (by decide : pair 4 5 ≠ pair 0 1) hp
  apply top_unique
  intro v _
  by_cases hv : v = 0
  · rw [hv]
    exact W.zero_mem
  obtain ⟨a, ha⟩ := NaturalTransport.transitive_nonzero z v hz0 hv
  rw [← ha]
  exact (subspaceCommutator_invariant rho ⊤ (alternatingGroup (Fin 6)) a.property z).mpr hz

end Model

namespace NaturalAction
variable {K : Type u} [Group K] [Finite K] {V : Subgroup K} [V.Normal]
  [IsElementaryAbelian 2 V] (d : NaturalAction V)

include d in
/-- The actual two-residual generates V by ambient commutators. -/
theorem module_le_residual_commutator : V ≤ ⁅V,pResidual 2 K⁆ := by
  have hspan : subspaceCommutator d.ρ ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
    have he := subspaceCommutator_map_embedding d.ρ Model.rho
      (MonoidHom.id Model.S) d.linearCoordinates.symm.toLinearMap
      (fun g v => by
        apply d.linearCoordinates.injective
        change d.linearCoordinates (d.ρ g (d.linearCoordinates.symm v)) =
          d.linearCoordinates (d.linearCoordinates.symm (Model.rho g v))
        rw [d.equivariant, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
      (alternatingGroup (Fin 6)) ⊤
    rw [Submodule.map_top, LinearEquiv.range, Subgroup.map_id,
      Model.moved_alternating_eq_top, Submodule.map_top, LinearEquiv.range] at he
    exact he
  have hc : Representation.NormalElementaryQuotient.commutatorSpace V (pResidual 2 K) = ⊤ := by
    rw [Representation.NormalElementaryQuotient.commutatorSpace_eq V d.q d.onto d.kernel_centralizer,
      d.residual_image]
    exact hspan
  intro v hv
  have hm : Additive.ofMul (⟨v,hv⟩ : V) ∈
      Representation.NormalElementaryQuotient.commutatorSpace V (pResidual 2 K) := by
    rw [hc]
    exact Submodule.mem_top
  exact hm

end NaturalAction
namespace SourceData
variable {K : Type u} [Group K] [Finite K] {L V : Subgroup K}
  [L.Normal] [V.Normal] {T : Sylow 2 K}

/-- The original C.1.37 data satisfy the module-generation condition. -/
theorem module_le_residual_commutator (d : SourceData L V T) : V ≤ ⁅V,pResidual 2 K⁆ := by
  let := d.elementary
  exact d.canonicalAction.module_le_residual_commutator

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
