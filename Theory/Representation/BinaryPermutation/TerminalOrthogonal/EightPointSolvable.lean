module
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightSylow
public import Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockResidual

/-!
# Solvability of the Sylow-fixed point stabilizer in the permutation six-space

A nonzero vector fixed by an A₈ Sylow two-subgroup has full S₈ stabilizer
conjugate to the unordered four-block stabilizer. Its two-core quotient
has normal three-core and a two-group quotient, so the stabilizer is solvable.

Source: Aschbacher--Smith, the paragraph following12.6.29, printed p.835;
the action is the original six-dimensional section of the binary permutation module.
-/

public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.Eight
private theorem four_block_solvable : Group.IsSolvable FourBlockResidual.H := by
  let Q := FourBlockResidual.H ⧸ pCore 2 FourBlockResidual.H
  let : Group.IsNilpotent (pCore 2 FourBlockResidual.H) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (pCore 3 Q) := pCore_isPGroup.isNilpotent
  let : Group.IsNilpotent (Q ⧸ pCore 3 Q) :=
    Theory.SpecificGroups.SymmetricEight.FourBlockQuotient.threeCore_quotient_two.isNilpotent
  let : Group.IsSolvable Q := Group.isSolvable_of_ker_le_range
    (pCore 3 Q).subtype (QuotientGroup.mk' (pCore 3 Q))
    (by rw [range_subtype,QuotientGroup.ker_mk'])
  exact Group.isSolvable_of_ker_le_range
    (pCore 2 FourBlockResidual.H).subtype (QuotientGroup.mk' (pCore 2 FourBlockResidual.H))
    (by rw [range_subtype,QuotientGroup.ker_mk'])

/-- The actual full permutation stabilizer of an A₈-Sylow-fixed nonzero
vector is solvable. -/
theorem sylow_fixed_stabilizer_solvable (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val v = v) :
    Group.IsSolvable (BinaryNaturalDual.VectorStabilizers.representationStabilizer (naturalRepresentation (Fin 8)) v) := by
  obtain ⟨r,hr⟩ := alternating_exists_conjugate_stabilizer Q v hv hfixed
  let : Group.IsSolvable FourBlockResidual.H := four_block_solvable
  let C := BinaryNaturalDual.VectorStabilizers.representationStabilizer (naturalRepresentation (Fin 8)) v
  let f : C →* FourBlockResidual.H :=
    (((MulAut.conj r.val).toMonoidHom).comp C.subtype).codRestrict _
      (fun x => (hr _).mp x.property)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply (MulAut.conj r.val).injective
    exact congrArg Subtype.val h
  exact Group.isSolvable_of_isSolvable_injective hf
end BinaryPermutation.TerminalOrthogonal.Eight
