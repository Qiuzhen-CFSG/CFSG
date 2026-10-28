module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Raw
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.OrbitData

/-!
# The projective orbit identifies the kernel of the marked projection

Generator equivariance propagates to the subgroup of matrix/permutation pairs.
An element in the kernel fixes every labelled line, so the checked projective
frame makes its matrix scalar. Thus the bridge uses the exact degree-4060
permutations, rather than order comparisons or semi-presentation recognition.
The two finite geometric certificates remain explicit inputs.
-/

namespace Rudvalis.Multiplier.DoubleCover
public section

private def linePreservers : Subgroup (Matˣ × Rudvalis.Model) where
  carrier := {g | ∀ i : Fin 4060, ∃ u : (ZMod 5)ˣ,
    (g.1 : Mat).mulVec (lineVector i) = (u : ZMod 5) • lineVector (g.2 • i)}
  one_mem' := by
    intro i
    refine ⟨1, ?_⟩
    simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mulVec, one_smul]
  mul_mem' := by
    intro x y hx hy i
    obtain ⟨u, hu⟩ := hy i
    obtain ⟨v, hv⟩ := hx (y.2 • i)
    refine ⟨u * v, ?_⟩
    change ((x.1 : Mat) * (y.1 : Mat)).mulVec (lineVector i) =
      ((u * v : (ZMod 5)ˣ) : ZMod 5) • lineVector ((x.2 * y.2) • i)
    rw [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, hv,
      smul_smul, Units.val_mul, mul_smul x.2 y.2 i]
  inv_mem' := by
    intro g hg i
    obtain ⟨u, hu⟩ := hg (g.2⁻¹ • i)
    rw [smul_inv_smul] at hu
    have hv := congrArg (fun v : Vec => ((g.1⁻¹ : Matˣ) : Mat).mulVec v) hu
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_smul] at hv
    refine ⟨u⁻¹, ?_⟩
    change ((g.1⁻¹ : Matˣ) : Mat).mulVec (lineVector i) =
      ((u⁻¹ : (ZMod 5)ˣ) : ZMod 5) • lineVector (g.2⁻¹ • i)
    rw [hv, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- The proposed orbit is equivariant for every element of the actual paired group. -/
theorem raw_preserves_lines (horbit : OrbitEquivariance) (x : Raw) (i : Fin 4060) :
    ∃ u : (ZMod 5)ˣ, (x.val.1 : Mat).mulVec (lineVector i) =
      (u : ZMod 5) • lineVector (projection x • i) := by
  have hle : pairSubgroup ≤ linePreservers := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | hg)
    · exact horbit.1
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact horbit.2
  exact hle x.property i

/-- Both concrete geometric certificates imply scalarity of the projection kernel. -/
theorem scalarKernel_of_geometry (horbit : OrbitEquivariance) (hframe : FrameRigidity) :
    ScalarKernel := by
  intro x hx
  apply hframe x.val.1
  intro i
  obtain ⟨u, hu⟩ := raw_preserves_lines horbit x i
  refine ⟨u, ?_⟩
  simpa only [hx, one_smul] using hu

end
end Rudvalis.Multiplier.DoubleCover
