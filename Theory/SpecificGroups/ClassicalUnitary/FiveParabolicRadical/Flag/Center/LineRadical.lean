module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Split

/-!
# Centralizing the line radical in the unitary-five residual

In the faithful radical–SU₃ semidirect product, an element centralizing the
radical acts trivially on its vector quotient. Lifting every vector with a
trace-one scalar forces the SU₃ matrix to be the identity. The remaining
radical coordinate is central, hence has zero vector coordinate. Every Levi
matrix fixes such a scalar coordinate, so the element is central in the whole
semidirect product.

We transport this calculation through the faithful projective embedding. It
applies to the center of a common Sylow subgroup once the line radical is
contained in that Sylow and the Sylow is contained in the line residual.

Source: the classical unitary calculation for the labeling in Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(I), case (7), printed pp.262--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
open Theory.SpecificGroups.UnitaryFive.LineCore
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
namespace Theory.SpecificGroups.UnitaryFive.Flag.Center
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

private theorem right_eq_one_of_commutes_inl (c : F) (hc : c + J.conj c = 1)
    (x : RadicalLevi J)
    (hx : ∀ u : Coord J, SemidirectProduct.inl u * x = x * SemidirectProduct.inl u) :
    x.right = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have h := congrArg (fun y : RadicalLevi J => y.left.vector)
    (hx (Coord.liftVector c hc v))
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.right_inl, map_one, MulAut.one_apply, Coord.mul_vector,
    Coord.liftVector_vector, leviAction_vector] at h
  rw [add_comm v] at h
  simpa only [Subgroup.coe_one, Units.val_one, one_mulVec] using (add_left_cancel h).symm

/-- The centralizer of the full radical is the center of its radical–SU₃ product. -/
theorem centralizer_inl_eq_center (c : F) (hc : c + J.conj c = 1) :
    Subgroup.centralizer ((SemidirectProduct.inl : Coord J →* RadicalLevi J).range :
      Set (RadicalLevi J)) = Subgroup.center (RadicalLevi J) := by
  apply le_antisymm
  · intro x hx
    have hcomm (u : Coord J) :
        SemidirectProduct.inl u * x = x * SemidirectProduct.inl u :=
      (Subgroup.mem_centralizer_iff.mp hx) _ ⟨u, rfl⟩
    have hr := right_eq_one_of_commutes_inl J c hc x hcomm
    have hl : x.left ∈ Subgroup.center (Coord J) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h := congrArg SemidirectProduct.left (hcomm u)
      simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, hr, map_one, MulAut.one_apply] using h
    have hv := (Coord.mem_center_iff_vector_eq_zero c hc x.left).mp hl
    rw [Subgroup.mem_center_iff]
    intro y
    apply SemidirectProduct.ext
    · have ha : leviAction J y.right x.left = x.left := by
        apply Coord.ext
        · simp only [leviAction_vector, hv, mulVec_zero]
        · rfl
      simp only [SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply, ha]
      exact Subgroup.mem_center_iff.mp hl y.left
    · simp only [SemidirectProduct.mul_right, hr, mul_one, one_mul]
  · exact Subgroup.center_le_centralizer _

/-- In the actual projective subgroup, centralizing the radical implies centrality. -/
theorem commute_of_centralizes_projectiveUnipotent
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    {z g : lineParabolic J}
    (hz : z ∈ radicalLeviSubgroup J hJ) (hg : g ∈ radicalLeviSubgroup J hJ)
    (hcomm : z ∈ Subgroup.centralizer (projectiveUnipotent J hJ : Set (lineParabolic J))) :
    g * z = z * g := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := hg
  have hx : x ∈ Subgroup.centralizer
      ((SemidirectProduct.inl : Coord J →* RadicalLevi J).range : Set (RadicalLevi J)) := by
    rintro _ ⟨u, rfl⟩
    apply radicalLeviMap_injective J hJ
    rw [map_mul, map_mul]
    simpa only [radicalLeviMap, SemidirectProduct.lift_inl] using
      Subgroup.mem_centralizer_iff.mp hcomm (toParabolic J hJ u) ⟨u, rfl⟩
  rw [centralizer_inl_eq_center J c hc] at hx
  simpa only [map_mul] using
    congrArg (radicalLeviMap J hJ) (Subgroup.mem_center_iff.mp hx y)

end Theory.SpecificGroups.UnitaryFive.Flag.Center
