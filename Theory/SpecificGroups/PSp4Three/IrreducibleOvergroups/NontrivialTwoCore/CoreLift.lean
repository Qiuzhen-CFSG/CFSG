module

public import Theory.SpecificGroups.PSp4Three.IrreducibleOvergroups.Reduction
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Theory.GroupTheory.PCoreSurjective

/-!
# Lifting the projective two-core

The kernel of the projection from a full symplectic preimage is a two-group:
central symplectic matrices are scalar, and preservation of a hyperbolic pair
forces their squares to be one. Consequently the full preimage's two-core is
exactly the inverse image of the projective two-core. A nontrivial projective
two-core thus gives a lift core strictly larger than the scalar kernel.
Nonsolvability also passes from the projective subgroup to its full preimage.

These are preliminary reductions, with no maximal-subgroup or extraspecial
classification assumed. Source application: Aschbacher–Smith, Theorem 0.1.2(4),
condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSp4Three

/-- In positive symplectic rank, every central element has square one. -/
public theorem central_square_eq_one {F : Type*} [Field F] {n : ℕ} [NeZero n]
    (g : Sp n F) (hg : g ∈ Subgroup.center (Sp n F)) : g ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := central_is_scalar g hg
  let u : Vector n F := e 0
  let v : Vector n F := f 0
  have hp : form (g • u) (g • v) = form u v := preserves g u v
  rw [ha, ha] at hp
  have ha2 : a * a = 1 := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_f_right,
      u, v, e, Pi.single_eq_same, mul_one] using hp
  apply ext_action
  intro x
  rw [pow_two, mul_smul, ha, ha, smul_smul, ha2, one_smul, one_smul]

/-- The actual scalar kernel in the full inverse image is a two-group. -/
public theorem preimageProjection_ker_isPGroup (M : Subgroup (PSp 2 (ZMod 3))) :
    IsPGroup 2 (preimageProjection M).ker := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change x.val.val ^ (2 ^ 1) = 1
  have hx : x.val.val ∈ Subgroup.center (Sp 2 (ZMod 3)) := by
    apply (show (projection (n := 2) (F := ZMod 3)).ker ≤
      Subgroup.center (Sp 2 (ZMod 3)) from projection_kernel.le)
    exact congrArg Subtype.val x.prop
  simpa only [pow_one] using central_square_eq_one x.val.val hx

/-- Taking the two-core commutes with this full inverse image. -/
public theorem fullPreimage_twoCore_comap (M : Subgroup (PSp 2 (ZMod 3))) :
    (pCore 2 M).comap (preimageProjection M) = pCore 2 (fullPreimage M) :=
  (preimageProjection M).comap_pCore_of_ker_isPGroup
    (preimageProjection_surjective M) (preimageProjection_ker_isPGroup M)

/-- The lifted two-core maps onto the projective two-core. -/
public theorem fullPreimage_twoCore_map (M : Subgroup (PSp 2 (ZMod 3))) :
    (pCore 2 (fullPreimage M)).map (preimageProjection M) = pCore 2 M := by
  rw [← fullPreimage_twoCore_comap, Subgroup.map_comap_eq_self]
  rw [(preimageProjection M).range_eq_top_of_surjective (preimageProjection_surjective M)]
  exact le_top

/-- A nontrivial projective two-core cannot lift entirely into the scalar kernel. -/
public theorem fullPreimage_twoCore_not_le_kernel (M : Subgroup (PSp 2 (ZMod 3)))
    (hM : pCore 2 M ≠ ⊥) :
    ¬ pCore 2 (fullPreimage M) ≤ (preimageProjection M).ker := by
  intro h
  apply hM
  rw [← fullPreimage_twoCore_map M]
  exact (Subgroup.map_eq_bot_iff _).mpr h

/-- A nonsolvable projective subgroup has nonsolvable full inverse image. -/
public theorem fullPreimage_not_isSolvable (M : Subgroup (PSp 2 (ZMod 3)))
    (hM : ¬ Group.IsSolvable M) : ¬ Group.IsSolvable (fullPreimage M) := by
  intro h
  exact hM (Group.isSolvable_of_surjective (preimageProjection_surjective M))

end Matrix.PSp4Three
