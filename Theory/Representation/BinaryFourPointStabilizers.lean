module
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Maximality
public import Theory.SpecificGroups.BinaryLinear.LineRadicalNormal
public import Theory.Representation.BinaryNaturalDual.Transport
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightSylow
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Maximality

/-!
# Maximal point stabilizers for the binary-four actions

A nonzero vector in the natural four-space has the maximal line parabolic
as stabilizer. A nonzero Sylow-fixed vector in the alternating-eight
six-space has a conjugate of the maximal even four-block stabilizer.
Both conclusions concern the actual stabilizer in the given representation.
Source application: Aschbacher--Smith, 10.2.9, printed pp.752--753.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryFourPointStabilizers
open scoped MatrixGroups
open BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic
/-- Every nonzero natural binary-four point has maximal stabilizer. -/
theorem natural_isCoatom (v : Fin 4 → ZMod 2) (hv : v ≠ 0) :
    IsCoatom (representationStabilizer (specialLinearNatural (k := ZMod 2) 4) v) := by
  let e := slEquivLinear 4
  have he : representationStabilizer (specialLinearNatural (k := ZMod 2) 4) v =
      (BinaryLinear.parabolic (Submodule.span (ZMod 2) {v})).comap e.toMonoidHom := by
    rw [BinaryLinear.LineRadical.parabolic_eq_point_stabilizer v hv]
    rfl
  rw [he]
  apply isCoatom_comap_of_surjective e.surjective
  apply BinaryLinear.FourParabolicAction.parabolic_isCoatom
  · intro hh
    exact hv ((_root_.Submodule.mem_bot (ZMod 2)).mp (hh ▸ Submodule.mem_span_singleton_self v))
  · intro hh
    have hc := finrank_span_singleton (K := ZMod 2) hv
    rw [hh,finrank_top,Module.finrank_fin_fun] at hc
    omega

/-- A nonzero Sylow-fixed vector of the alternating-eight natural six-space
has maximal stabilizer in the actual alternating group. -/
theorem orthogonal_isCoatom (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (v : BinaryPermutation.natural (Fin 8)) (hv : v ≠ 0)
    (hfix : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      BinaryPermutation.naturalRepresentation (Fin 8) g.val v = v) :
    IsCoatom (representationStabilizer
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) v) := by
  obtain ⟨r,hr⟩ := BinaryPermutation.TerminalOrthogonal.Eight.alternating_exists_conjugate_stabilizer
    Q v hv hfix
  have he : representationStabilizer
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) v =
      (Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer.subgroupOf
        (alternatingGroup (Fin 8))).comap (MulAut.conj r).toMonoidHom := by
    ext g
    exact hr g.val
  rw [he]
  exact isCoatom_comap_of_surjective (MulAut.conj r).surjective
    Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.fourStabilizer_subgroupOf_isCoatom
end Representation.BinaryFourPointStabilizers
