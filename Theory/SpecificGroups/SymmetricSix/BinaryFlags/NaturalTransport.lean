module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-!
# Transitivity on the genuine binary six-letter natural module

The fifteen nonzero vectors are the literal duad classes. An even permutation
moving the distinguished duad to any prescribed duad gives transitivity.
The two swaps constructing the mover are corrected by a swap fixing the
original duad when needed. Only the fifteen mover identities are checked
by finite reduction; arbitrary vectors use the established duad parametrization.

Source: Aschbacher–Smith, §B.3 and Hypothesis 13.7.1, printed pp.83–85, 935.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
open BinaryPermutation NaturalGeometry

private def mover (d : NaturalGeometry.Duad) : Equiv.Perm (Fin 6) :=
  let g := Equiv.swap ((Equiv.swap 4 d.val.1) 5) d.val.2 * Equiv.swap 4 d.val.1
  if g ∈ alternatingGroup (Fin 6) then g else g * Equiv.swap 0 1

set_option maxRecDepth 4096 in
private theorem mover_spec : ∀ d : NaturalGeometry.Duad,
    mover d ∈ alternatingGroup (Fin 6) ∧
      mover d 4 = d.val.1 ∧ mover d 5 = d.val.2 := by decide +kernel

/-- Every nonzero vector is the image of the distinguished duad under A₆. -/
theorem exists_even_image (v : natural (Fin 6)) (hv : v ≠ 0) :
    ∃ g : alternatingGroup (Fin 6),
      naturalRepresentation (Fin 6) g.val (pairVector 4 5) = v := by
  obtain ⟨d, rfl⟩ := (vector_cases v).resolve_left hv
  refine ⟨⟨mover d, (mover_spec d).1⟩, ?_⟩
  rw [pairVector_map]
  change pairVector (mover d 4) (mover d 5) = duadVector d
  rw [(mover_spec d).2.1, (mover_spec d).2.2]
  rfl

/-- Transitivity on the nonzero vectors of the actual augmentation quotient. -/
theorem transitive_nonzero (v w : natural (Fin 6)) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : alternatingGroup (Fin 6), naturalRepresentation (Fin 6) g.val v = w := by
  obtain ⟨a, ha⟩ := exists_even_image v hv
  obtain ⟨b, hb⟩ := exists_even_image w hw
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha]
  change naturalRepresentation (Fin 6) (b.val * a.val⁻¹)
    (naturalRepresentation (Fin 6) a.val (pairVector 4 5)) = w
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, hb]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
