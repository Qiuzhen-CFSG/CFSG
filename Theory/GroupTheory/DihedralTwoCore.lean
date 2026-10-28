module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Central two-cores of odd-dihedral products

The two-core of a finite group is central whenever the group is isomorphic to
the product of a dihedral group with odd rotation order and an abelian group.
The abelian factor need not be a two-group, and rotation order one is allowed.
This elementary fact supplies the quotient-core centrality needed in the
coatom-to-stabilizer transfer in the distance-one argument of Stellmacher (9.1).

Project the two-core to a normal two-subgroup of the dihedral factor. Any
rotation in this image has order dividing both the odd rotation order and a
power of two, so it is trivial. Every dihedral commutator is a rotation;
normality therefore makes every commutator with the image trivial. Centrality
in the product follows from commutativity of the second factor and transports
back through the isomorphism. This argument covers rotation order one without
requiring the dihedral two-core itself to be trivial.
-/

private theorem normal_two_subgroup_dihedral_le_center {order : ℕ} (hodd : Odd order)
    (normalSubgroup : Subgroup (DihedralGroup order)) [normalSubgroup.Normal]
    (htwo : IsPGroup 2 normalSubgroup) :
    normalSubgroup ≤ Subgroup.center (DihedralGroup order) := by
  have hrotation (index : ZMod order) (hmem : DihedralGroup.r index ∈ normalSubgroup) :
      DihedralGroup.r index = 1 := by
    obtain ⟨exponent, hexponent⟩ := htwo ⟨DihedralGroup.r index, hmem⟩
    have hpow : DihedralGroup.r index ^ (2 ^ exponent) = 1 :=
      congrArg Subtype.val hexponent
    have hoddpow : DihedralGroup.r index ^ order = 1 := by
      simp [DihedralGroup.r_pow]
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_left.mpr hodd).pow_left exponent)
      (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hoddpow))
  intro element helement
  apply Subgroup.mem_center_iff.mpr
  intro other
  have hmem := normalSubgroup.mul_mem
    (Subgroup.Normal.conj_mem inferInstance element helement other)
    (normalSubgroup.inv_mem helement)
  have hone : other * element * other⁻¹ * element⁻¹ = 1 := by
    cases element <;> cases other <;>
      simp only [DihedralGroup.inv_r, DihedralGroup.inv_sr, DihedralGroup.r_mul_r,
        DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] at hmem ⊢ <;>
      exact hrotation _ hmem
  rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hone

/-- An odd-dihedral factor and an abelian factor force the two-core to be central. -/
public theorem dihedralProduct_twoCore_le_center
    (K C : Type*) [Group K] [Finite K] [Group C] [Finite C]
    [IsMulCommutative C] (order : ℕ) (hodd : Odd order)
    (hmodel : Nonempty (K ≃* (DihedralGroup order × C))) :
    pCore 2 K ≤ Subgroup.center K := by
  obtain ⟨model⟩ := hmodel
  let projection : K →* DihedralGroup order := (MonoidHom.fst _ _).comp model.toMonoidHom
  have hsurj : Function.Surjective projection := by
    intro element
    obtain ⟨preimage, hpreimage⟩ := model.surjective (element, 1)
    exact ⟨preimage, congrArg Prod.fst hpreimage⟩
  let image := (pCore 2 K).map projection
  have himageNormal : image.Normal :=
    Subgroup.Normal.map inferInstance projection hsurj
  have himageCenter := normal_two_subgroup_dihedral_le_center hodd image
    (pCore_isPGroup.map projection)
  intro element helement
  apply Subgroup.mem_center_iff.mpr
  intro other
  apply model.injective
  simp only [map_mul]
  apply Prod.ext
  · exact Subgroup.mem_center_iff.mp
      (himageCenter (Subgroup.mem_map.mpr ⟨element, helement, rfl⟩)) (projection other)
  · exact mul_comm' (model other).2 (model element).2
