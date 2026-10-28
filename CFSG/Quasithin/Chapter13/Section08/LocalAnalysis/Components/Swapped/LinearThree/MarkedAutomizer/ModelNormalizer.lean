module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.InvariantLines
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The intrinsic normalizer of the marked cover residual

The two-residual of a binary point stabilizer in A₆ is the tetrahedral
subgroup fixing the corresponding duad pointwise. Its normalizer is the
original point stabilizer, as checked on the actual six-letter action.
Residuals commute with the coordinate quotient from the hexacode cover,
so its marked residual has exactly the marked cover parabolic as normalizer.
Consequently every cover automorphism preserving the residual preserves
both intrinsic cubic-direction candidates, without a prescribed action.

Source: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2, pp.877–878,
used in the marked automizer calculation of 13.8.16(1), printed p.952
(PDF p.969). The orders and independence of the two directions and their
identification with the source marks are separate obligations.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Model

private theorem symmetric_residual : pResidual 2 (Equiv.Perm (Fin 4)) = alternatingGroup (Fin 4) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 4)).index = 2 ^ 1
    simp
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro g hg
    apply mem_pResidual_of_orderOf_coprime
    rw [Equiv.Perm.IsThreeCycle.orderOf hg]
    decide

private def tetra : Subgroup A6 :=
  MulAction.stabilizer A6 (0 : Fin 6) ⊓ MulAction.stabilizer A6 (1 : Fin 6)

private theorem tetra_model :
    (alternatingGroup (Fin 4)).map
      (a6DuadStabilizer.subtype.comp a6DuadModelToStabilizer) = tetra := by
  ext g
  simp only [mem_map, Subtype.ext_iff]
  change (∃ p : Equiv.Perm (Fin 4), p.sign = 1 ∧ a6DuadModelHom p = g.val) ↔
    g.val 0 = 0 ∧ g.val 1 = 1
  revert g
  decide +kernel

private theorem duad_residual :
    (pResidual 2 a6DuadStabilizer).map a6DuadStabilizer.subtype = tetra := by
  rw [← map_pResidual 2 a6DuadModelEquiv, symmetric_residual, map_map]
  exact tetra_model

set_option maxRecDepth 100000 in
private theorem tetra_normalizer : normalizer (tetra : Set A6) = a6DuadStabilizer := by
  ext g
  change (∀ n : A6, (n.val 0 = 0 ∧ n.val 1 = 1) ↔
      ((g * n * g⁻¹).val 0 = 0 ∧ (g * n * g⁻¹).val 1 = 1)) ↔
    g ∈ a6DuadStabilizer
  revert g
  decide +kernel

private theorem point_stabilizer_conjugate (x : BinaryPoint) :
    ∃ g : A6, MulAction.stabilizer A6 x =
      a6DuadStabilizer.map (MulAut.conj g).toMonoidHom := by
  have he : MulAction.stabilizer A6 x =
      MulAction.stabilizer A6 (duadPolarEquiv.symm x) := by
    ext g
    change g.val • x = x ↔ g.val • duadPolarEquiv.symm x = duadPolarEquiv.symm x
    rw [← duadPolarEquiv.injective.eq_iff, duadPolarEquiv_equivariant]
    simp
  obtain ⟨g, hg⟩ := a6_duad_transitive 0 (duadPolarEquiv.symm x)
  refine ⟨g, ?_⟩
  rw [he, ← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    a6_duad_stabilizer_zero]

theorem point_residual_normalizer (x : BinaryPoint) :
    normalizer (((pResidual 2 (MulAction.stabilizer A6 x)).map
      (MulAction.stabilizer A6 x).subtype : Subgroup A6) : Set A6) =
      MulAction.stabilizer A6 x := by
  obtain ⟨g, hg⟩ := point_stabilizer_conjugate x
  have hr : (pResidual 2 (MulAction.stabilizer A6 x)).map
      (MulAction.stabilizer A6 x).subtype =
      ((pResidual 2 a6DuadStabilizer).map a6DuadStabilizer.subtype).map
        (MulAut.conj g).toMonoidHom := by
    rw [map_embedded_pResidual, ← hg]
  rw [hr, ← map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
    duad_residual, tetra_normalizer, ← hg]

theorem residual_coordinate_image (x : BinaryPoint) :
    (residual x).map Atlas.Codes.hexEvenCoordinate =
      (pResidual 2 (MulAction.stabilizer A6 x)).map
        (MulAction.stabilizer A6 x).subtype := by
  rw [residual, map_embedded_pResidual]
  have hp : (parabolic x).map Atlas.Codes.hexEvenCoordinate = MulAction.stabilizer A6 x := by
    exact map_comap_eq_self_of_surjective Atlas.Codes.hexEvenCoordinate_surjective _
  rw [hp]

theorem residual_normalizer (x : BinaryPoint) :
    normalizer (residual x : Set Cover) = parabolic x := by
  apply le_antisymm
  · intro g hg
    have hm : Atlas.Codes.hexEvenCoordinate g ∈
        normalizer ((residual x).map Atlas.Codes.hexEvenCoordinate : Set A6) :=
      (residual x).le_normalizer_map Atlas.Codes.hexEvenCoordinate ⟨g, hg, rfl⟩
    rw [residual_coordinate_image, point_residual_normalizer] at hm
    exact hm
  · unfold residual
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pResidual 2 (parabolic x)).le_normalizer_map (parabolic x).subtype

/-- Residual preservation alone forces preservation of the derived direction;
the parabolic-normalization premise is discharged by the actual model. -/
theorem sectionAut_preserves_derivedLine (x : BinaryPoint) (a : MulAut Cover)
    (ha : (residual x).map a.toMonoidHom = residual x) :
    (derivedLine x).map (sectionAut x a ha).toMonoidHom = derivedLine x :=
  sectionAut_derivedLine x a ha
    (parabolic_preserved_of_normalizer_eq x (residual_normalizer x) a ha)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.Model

end
