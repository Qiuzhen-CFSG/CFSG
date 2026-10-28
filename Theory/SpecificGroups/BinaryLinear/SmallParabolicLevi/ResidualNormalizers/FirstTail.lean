module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.ResidualNormalizers.EndpointActions
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
/-!
# The first-node action on the quotient three-space is a two-group

The first single-node parabolic preserves the cuts of dimensions two, three
and four. After quotienting by the two-space, the classes of `b 2`, `b 3`
and `b 4` give coordinates in which its actual action is upper triangular.
Invertibility over the binary field forces all three diagonal entries to be
one. The image therefore embeds in the upper unitriangular group, whose
two-group property follows from Cayley--Hamilton and Frobenius.

Source application: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.8.25, printed p.960 (PDF p.977), the first-node residual normalizer in
binary five-space. This supplies the first endpoint action-image premise
of the residual-normalizer calculation.
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace BinaryLinear.SmallParabolicLevi.ResidualNormalizers

private theorem mem_flagSpace_iff_coordinates (b : FiveBasis) (k : Fin 4) (v : Space 5) :
    v ∈ flagSpace b k ↔ ∀ j : Fin 5, k.val < j.val → b.repr v j = 0 := by
  rw [flagSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private noncomputable def tailProjection (b : FiveBasis) : Space 5 →ₗ[ZMod 2] Space 3 :=
  LinearMap.pi fun i => b.coord (Fin.natAdd 2 i)

private theorem tailProjection_ker (b : FiveBasis) :
    (tailProjection b).ker = flagSpace b 1 := by
  ext v
  rw [LinearMap.mem_ker, mem_flagSpace_iff_coordinates]
  constructor
  · intro hv j hj
    let i : Fin 3 := ⟨j.val - 2, by have := j.isLt; omega⟩
    have he : Fin.natAdd 2 i = j := Fin.ext (by dsimp [i]; omega)
    have h := congrFun hv i
    change b.repr v (Fin.natAdd 2 i) = 0 at h
    simpa only [he] using h
  · intro hv
    funext i
    exact hv (Fin.natAdd 2 i) (by change 1 < 2 + i.val; omega)

private theorem tailProjection_surjective (b : FiveBasis) :
    Function.Surjective (tailProjection b) := by
  intro v
  refine ⟨b.equivFun.symm (Fin.append (0 : Fin 2 → ZMod 2) v), ?_⟩
  funext i
  change b.equivFun (b.equivFun.symm _) (Fin.natAdd 2 i) = v i
  rw [b.equivFun.apply_symm_apply, Fin.append_right]

private noncomputable def tailCoordinates (b : FiveBasis) :
    (Space 5 ⧸ flagSpace b 1) ≃ₗ[ZMod 2] Space 3 :=
  (Submodule.quotEquivOfEq _ _ (tailProjection_ker b).symm).trans
    ((tailProjection b).quotKerEquivOfSurjective (tailProjection_surjective b))

private theorem tailCoordinates_mk (b : FiveBasis) (v : Space 5) :
    tailCoordinates b ((flagSpace b 1).mkQ v) = tailProjection b v := rfl

private theorem tailCoordinates_basis (b : FiveBasis) (j : Fin 3) :
    tailCoordinates b ((flagSpace b 1).mkQ (b (Fin.natAdd 2 j))) = Pi.single j 1 := by
  rw [tailCoordinates_mk]
  funext i
  have he : (Fin.natAdd 2 j = Fin.natAdd 2 i) ↔ j = i := by
    constructor
    · intro h
      apply Fin.ext
      have := congrArg Fin.val h
      dsimp at this
      omega
    · exact congrArg (Fin.natAdd 2)
  simp [tailProjection, Module.Basis.coord_apply, Finsupp.single_apply, Pi.single_apply,
    he, eq_comm]

private noncomputable def tailLinearTransport (b : FiveBasis) :
    BinaryLinear.GL (Space 5 ⧸ flagSpace b 1) ≃* LinearGroup 3 :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (tailCoordinates b)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _))

private noncomputable def tailMatrixEquiv (b : FiveBasis) :
    BinaryLinear.GL (Space 5 ⧸ flagSpace b 1) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (tailLinearTransport b).trans (slEquivLinear 3).symm

private theorem tailMatrix_mulVec (b : FiveBasis)
    (f : BinaryLinear.GL (Space 5 ⧸ flagSpace b 1)) (v : Space 3) :
    (tailMatrixEquiv b f).val.mulVec v =
      tailCoordinates b (f ((tailCoordinates b).symm v)) := by
  rw [← slEquivLinear_apply]
  change slEquivLinear 3 ((slEquivLinear 3).symm (tailLinearTransport b f)) v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

private theorem tailMatrix_apply (b : FiveBasis)
    (g : flagStabilizer b ({0} : Set (Fin 4))ᶜ) (i j : Fin 3) :
    (tailMatrixEquiv b (firstTailAction b g)).val i j =
      b.repr (g.val (b (Fin.natAdd 2 j))) (Fin.natAdd 2 i) := by
  have h := congrFun (tailMatrix_mulVec b (firstTailAction b g) (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply,
    ← tailCoordinates_basis b j, LinearEquiv.symm_apply_apply] at h
  exact h

private theorem tailMatrix_upper (b : FiveBasis)
    (g : flagStabilizer b ({0} : Set (Fin 4))ᶜ) :
    (tailMatrixEquiv b (firstTailAction b g)).val.IsUpperTriangular := by
  intro i j hji
  rw [tailMatrix_apply]
  have hlt : j.val < i.val := hji
  let k : Fin 4 := ⟨2 + j.val, by have := i.isLt; omega⟩
  have hk : k ∈ ({0} : Set (Fin 4))ᶜ := by
    change k ≠ 0
    intro he
    have he' := congrArg Fin.val he
    dsimp [k] at he'
    omega
  have hmem := (mem_flagStabilizer_iff_maps b _ g.val).mp g.property k hk
    (b (Fin.natAdd 2 j)) ((basis_mem_flagSpace_iff b k _).mpr (by rfl))
  exact (mem_flagSpace_iff_coordinates b k _).mp hmem (Fin.natAdd 2 i)
    (by change 2 + j.val < 2 + i.val; omega)

private theorem tailMatrix_unipotent (b : FiveBasis)
    (g : flagStabilizer b ({0} : Set (Fin 4))ᶜ) :
    tailMatrixEquiv b (firstTailAction b g) ∈
      Theory.SpecificGroups.LinearSylowNormalizers.unipotent 3 (ZMod 2) := by
  rw [Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent]
  have hu := tailMatrix_upper b g
  refine ⟨(Theory.SpecificGroups.LinearSylowNormalizers.mem_borel 3 (ZMod 2) _).mpr hu,
    fun i => ?_⟩
  have hd := (tailMatrixEquiv b (firstTailAction b g)).property
  rw [Matrix.det_of_isUpperTriangular hu] at hd
  have hp : (∏ j, (tailMatrixEquiv b (firstTailAction b g)).val j j) ≠ 0 := by
    rw [hd]
    exact one_ne_zero
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hi

/-- The actual first-node action on the quotient by the two-space has two-group image. -/
theorem firstTailAction_range_isPGroup (b : FiveBasis) :
    IsPGroup 2 (firstTailAction b).range := by
  rintro ⟨f, g, rfl⟩
  obtain ⟨n, hn⟩ :=
    Theory.SpecificGroups.LinearSylowNormalizers.unipotent_isPGroup 3 (ZMod 2)
      (by decide) ⟨tailMatrixEquiv b (firstTailAction b g), tailMatrix_unipotent b g⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply (tailMatrixEquiv b).injective
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
    congrArg Subtype.val hn

end BinaryLinear.SmallParabolicLevi.ResidualNormalizers

end
