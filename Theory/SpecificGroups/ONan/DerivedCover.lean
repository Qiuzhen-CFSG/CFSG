module

public import Theory.SpecificGroups.ONan.LinearCoverKernel
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# A perfect central cover inside the linear O'Nan model

The derived subgroup of the actual linear matrix group projects onto the
projective model whenever that model is perfect. The projective kernel is
central, so the derived group is itself perfect. A scalar in this derived
group has determinant one; hence its order divides both 45 and six. The
kernel therefore has order dividing three.

Perfectness of the model can be inherited from the source central-quotient
isomorphism. No ambient order or simplicity certificate is required. This
constructs a small central cover, but does not identify it as universal.

Sources: GLS3, Table 5.3s, printed p.280, and the matrix attribution in
`refs/original/onan/README.md`. The determinant argument only uses the
specified dimension and field, not the table's Schur multiplier assertion.
-/

namespace ONan.Cover

/-- The projective map restricted to the derived linear matrix group. -/
@[expose] public def derivedProjection : commutator linearSubgroup →* Model :=
  projection.comp (commutator linearSubgroup).subtype

/-- The kernel of the concrete projective map is central. -/
public theorem projection_ker_le_center : projection.ker ≤ Subgroup.center linearSubgroup := by
  intro x hx
  have hc : (x : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    exact congrArg Subtype.val hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc y)

/-- Perfectness downstairs makes the derived linear group project onto the model. -/
public theorem derivedProjection_surjective [Group.IsPerfect Model] :
    Function.Surjective derivedProjection := by
  have hmap : (commutator linearSubgroup).map projection = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr projection_surjective]
    exact Group.IsPerfect.commutator_eq_top
  intro y
  have hy : y ∈ (commutator linearSubgroup).map projection := by rw [hmap]; trivial
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, hxy⟩

/-- A scalar in the derived linear group has cube one: its determinant is one,
so its order divides both 45 and the order six of the scalar group. -/
public theorem derivedProjection_ker_pow_three (x : derivedProjection.ker) : x ^ 3 = 1 := by
  have hc : (x.val.val : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    exact congrArg Subtype.val x.property
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  have hd : u ^ 45 = 1 := by
    have h := Abelianization.commutator_subset_ker
      (Matrix.GeneralLinearGroup.det.comp linearSubgroup.subtype) x.val.property
    change Matrix.GeneralLinearGroup.det (x.val.val :
      Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) = 1 at h
    rw [← hu, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    exact h
  have h6 : u ^ 6 = 1 := by
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hn : Nat.card ((ZMod 7)ˣ) = 6 := by rw [Nat.card_units, Nat.card_zmod]
    simpa only [hn] using (pow_card_eq_one' (x := u))
  have h3 : u ^ 3 = 1 := by
    have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd)
      (orderOf_dvd_of_pow_eq_one h6)
    exact orderOf_dvd_iff_pow_eq_one.mp (by simpa using hdvd)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (x.val.val : Matrix.GeneralLinearGroup (Fin 45) (ZMod 7)) ^ 3 = 1
  rw [← hu, ← map_pow, h3, map_one]

/-- The derived projective kernel has order dividing three, independently of
any simplicity, order or universality assertion about the model. -/
public theorem derivedProjection_ker_card_dvd_three : Nat.card derivedProjection.ker ∣ 3 := by
  let j : derivedProjection.ker →* projection.ker :=
    ((commutator linearSubgroup).subtype.comp derivedProjection.ker.subtype).codRestrict _
      (fun x => x.property)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : projection.ker => z.val) h
  have hd : Nat.card derivedProjection.ker ∣ 6 :=
    (Subgroup.card_dvd_of_injective j hj).trans projection_ker_card_dvd_six
  have hn : ¬ 2 ∣ Nat.card derivedProjection.ker := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    have := orderOf_dvd_of_pow_eq_one (derivedProjection_ker_pow_three x)
    rw [hx] at this
    norm_num at this
  exact (Nat.prime_two.coprime_iff_not_dvd.mpr hn).symm.dvd_of_dvd_mul_left hd

/-- Restricting the projective map to the derived group preserves centrality. -/
public theorem derivedProjection_ker_le_center :
    derivedProjection.ker ≤ Subgroup.center (commutator linearSubgroup) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp (projection_ker_le_center hx) y)

/-- The derived group of a central extension of a perfect model is perfect. -/
public instance derived_isPerfect [Group.IsPerfect Model] :
    Group.IsPerfect (commutator linearSubgroup) :=
  PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center
    projection projection_surjective projection_ker_le_center

/-- A concrete perfect central cover with kernel of order at most three.
No universal property is asserted. -/
@[expose] public def derivedCover [Group.IsPerfect Model] :
    PerfectCentralCovering.Cover (commutator linearSubgroup) Model where
  toMonoidHom := derivedProjection
  surjective := derivedProjection_surjective
  isPerfect := inferInstance
  ker_le_center := derivedProjection_ker_le_center

end ONan.Cover
