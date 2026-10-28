module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Frames
public import Theory.AtlasPort.Janko2.Lattices.IcosianIntegralScalarAction

/-!
# The scalar field on the literal Leech fixed space

The actual scalar element `y` has a norm-one icosian lift of order three.
In the quaternion division ring that lift satisfies X² + X + 1 = 0.
Transport through the integral comparison and reduction modulo two proves
this polynomial for `y` on the entire Leech quotient, and hence excludes
nonzero Y-fixed vectors without a conjugacy marking or dimension assumption.

Y normalizes U, so the polynomial supplies a GF(4) module structure on the
literal U-fixed space. The established binary dimension bound gives dimension
at most six over that field. Elements centralizing I commute with Y and
therefore act linearly over GF(4). This is the representation-theoretic input
for the separate SL₃(4) local-subgroup and module-identification constructions;
it does not assert either construction or an inhabitant of `LongFrame`.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.283 (PDF147).
The integral scalar action and Leech comparison are the attributed ATLAS ports
imported above; their inverse-right-multiplication convention is retained.
-/

open Atlas.Algebra Atlas.Lattices Atlas.Conway Atlas.Codes
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
@[expose] public noncomputable section

private theorem scalar_apply (u : icosianNormOneGroup) (x : leech) :
    (icosianScalarsToCo0 u).val x =
      icosianLeechRightScalars (MulOpposite.op (icosianNormOneToOrder u⁻¹)) x := by
  obtain ⟨z, rfl⟩ := icosianLeechEquiv.surjective x
  apply Subtype.ext
  apply rationalEmbedding_injective
  rw [icosianLeechRightScalars_rational]
  have he := congrArg
    (fun g : rationalLatticeIsometries => g.val (rationalEmbedding (icosianLeechEquiv z).val))
    (icosianScalarsToCo0_extension u)
  change rationalExtension (icosianScalarsToCo0 u).val
    (rationalEmbedding (icosianLeechEquiv z).val) = _ at he
  rw [rationalExtension_agrees, icosianLeechEquiv_agrees] at he
  rw [he]
  change icosianComparison (icosianScalarRepresentation u
    (icosianComparison.symm (icosianComparison (icosianCoordinateEmbedding z.val)))) = _
  rw [icosianComparison.symm_apply_apply]
  rfl

private theorem scalar_cube_lift : ∃ u : icosianNormOneGroup,
    leechCentralProjection (icosianScalarsToCo0 u) = y ∧ u ^ 3 = 1 := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker
    (icosianScalarProjectiveAlternating.symm
      (alternatingGroup.ofSubtype fourPoints threeCycle))
  have he : leechCentralProjection (icosianScalarsToCo0 u) = y := by
    change icosianScalarProjectiveToCo1 (QuotientGroup.mk' _ u) = _
    rw [hu]
    rfl
  have hy : y ^ 3 = 1 := by rw [← y_order]; exact pow_orderOf_eq_one _
  have hp : leechCentralProjection ((icosianScalarsToCo0 u)^3) = 1 := by
    rw [map_pow, he, hy]
  have hk := MonoidHom.mem_ker.mpr hp
  rw [leechCentralProjection_kernel, leechCentralSigns_mem] at hk
  refine ⟨u^4, ?_, ?_⟩
  · rw [map_pow, map_pow, he]
    calc y^4 = y^3 * y := pow_succ _ 3
         _ = y := by rw [hy, one_mul]
  · apply icosianScalarsToCo0_injective
    rw [map_pow, map_pow, map_one, ← pow_mul,
      show 4 * 3 = 3 * 4 by decide, pow_mul]
    rcases hk with hk | hk
    · rw [hk, one_pow]
    · rw [hk, show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      have hn : negationIsometry^2 = 1 := negationIsometry_sq
      rw [hn, one_pow]

private theorem scalar_cube_polynomial (u : icosianNormOneGroup)
    (hu : u^3=1) (hne : u ≠ 1) :
    (icosianNormOneToOrder u)^2 + icosianNormOneToOrder u + 1 = 0 := by
  apply Subtype.ext
  change u.val.val^2 + u.val.val + 1 = 0
  have hc : u.val.val^3=1 := congrArg (fun v : icosianNormOneGroup => v.val.val) hu
  have hn : u.val.val - 1 ≠ 0 := by
    intro h
    exact hne (icosianNormOne_value_injective (sub_eq_zero.mp h))
  apply (mul_eq_zero.mp (show
      (u.val.val-1)*(u.val.val^2+u.val.val+1)=0 from by
    calc
      (u.val.val-1)*(u.val.val^2+u.val.val+1) = u.val.val^3-1 := by noncomm_ring
      _ = 0 := by rw [hc, sub_self])).resolve_left hn

private theorem right_scalar_polynomial (a : icosianOrderᵐᵒᵖ)
    (ha : a^2 + a + 1 = 0) (x : leech) :
    icosianLeechRightScalars a (icosianLeechRightScalars a x) +
      icosianLeechRightScalars a x + x = 0 := by
  have hlinear := congrArg icosianLeechRightScalars ha
  simp only [map_add, map_pow, map_one, map_zero] at hlinear
  have hx := congrArg (fun f : Module.End ℤ leech => f x) hlinear
  simpa only [pow_two, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply, LinearMap.zero_apply] using hx

/-- The literal scalar element Y satisfies its irreducible binary quadratic
on the entire Leech quotient, not just on the U-fixed subspace. -/
theorem y_polynomial (v : LeechModTwo) :
    quotientModTwoRepresentation y (quotientModTwoRepresentation y v) +
      quotientModTwoRepresentation y v + v = 0 := by
  obtain ⟨u, hu, hu3⟩ := scalar_cube_lift
  have hne : u ≠ 1 := by
    intro h
    have hy : y = 1 := by rw [← hu, h, map_one, map_one]
    have ho := y_order
    rw [hy, orderOf_one] at ho
    contradiction
  have hpoly := scalar_cube_polynomial u⁻¹ (by rw [inv_pow, hu3, inv_one])
    (by simpa using hne)
  have hop : (MulOpposite.op (icosianNormOneToOrder u⁻¹))^2 +
      MulOpposite.op (icosianNormOneToOrder u⁻¹) + 1 = 0 := by
    exact congrArg MulOpposite.op hpoly
  obtain ⟨x, rfl⟩ := leechReduction_surjective v
  have hx := right_scalar_polynomial _ hop x
  simp only [← scalar_apply] at hx
  rw [← hu, quotientModTwoRepresentation_compatible,
    leechModTwoRepresentation_reduce, leechModTwoRepresentation_reduce]
  have hr := congrArg leechReduction hx
  simpa only [map_add, map_zero] using hr

/-- The order-three scalar has no nonzero fixed vector, as used in Lemma 49.5. -/
theorem y_fixed_eq_zero (v : LeechModTwo)
    (hv : quotientModTwoRepresentation y v = v) : v = 0 := by
  have h := y_polynomial v
  rw [hv, hv] at h
  have hz : v + v = 0 := by
    have hz := two_smul (ZMod 2) v
    simpa using hz.symm
  simpa only [hz, zero_add] using h

/-- Normalizing U is sufficient to preserve its literal fixed space. -/
theorem normalizer_preserves {g : LeechCentralQuotient}
    (hg : g ∈ Subgroup.normalizer (U : Set LeechCentralQuotient)) {v : LeechModTwo} (hv : v ∈ fixedSpace) :
    quotientModTwoRepresentation g v ∈ fixedSpace := by
  intro u hu
  have hu' : g⁻¹ * u * g ∈ U :=
    ((Subgroup.mem_normalizer_iff''.mp hg) u).mp hu
  have he : u * g = g * (g⁻¹ * u * g) := by group
  calc
    quotientModTwoRepresentation u (quotientModTwoRepresentation g v) =
        quotientModTwoRepresentation (u * g) v := by rw [map_mul]; rfl
    _ = quotientModTwoRepresentation (g * (g⁻¹ * u * g)) v := by rw [he]
    _ = quotientModTwoRepresentation g v := by
      rw [map_mul]
      exact congrArg _ (hv _ hu')

/-- Y acts on the literal U-fixed subspace because I normalizes U. -/
def yEnd : Module.End Bit fixedSpace :=
  (quotientModTwoRepresentation y).toLinearMap.restrict
    (fun _v hv => normalizer_preserves (I_le_normalizer_U ⟨threeCycle, rfl⟩) hv)

/-- The restricted Y operator is a root of the defining quadratic for GF(4). -/
theorem yEnd_quadratic : yEnd * yEnd = (1 : Bit) • 1 + (1 : Bit) • yEnd := by
  ext v
  have h := y_polynomial v.val
  change quotientModTwoRepresentation y (quotientModTwoRepresentation y v.val) =
    (1 : Bit) • v.val + (1 : Bit) • quotientModTwoRepresentation y v.val
  simp only [one_smul]
  have hn (w : LeechModTwo) : -w = w := by
    have hz := two_smul Bit w
    have hz' : w + w = 0 := by simpa using hz.symm
    exact neg_eq_iff_add_eq_zero.mpr hz'
  calc
    quotientModTwoRepresentation y (quotientModTwoRepresentation y v.val) =
        -(quotientModTwoRepresentation y v.val + v.val) :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using h)
    _ = v.val + quotientModTwoRepresentation y v.val := by
      rw [neg_add, hn, hn, add_comm]

/-- The scalar field generated by the actual Y action. -/
def goldenScalars : GoldenFour →ₐ[Bit] Module.End Bit fixedSpace :=
  QuadraticAlgebra.lift ⟨yEnd, yEnd_quadratic⟩

/-- Identify the coordinate field with the quadratic scalar field. -/
def scalarFieldEquiv : F ≃+* GoldenFour := by
  letI : Fintype F := Fintype.ofFinite F
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide), goldenFour_card]
    norm_num)

/-- A named, scoped scalar structure avoids changing the existing binary API. -/
scoped instance fixedSpaceModule : Module F fixedSpace :=
  Module.compHom fixedSpace (goldenScalars.toRingHom.comp scalarFieldEquiv.toRingHom)

/-- Explicit scalar multiplication; only the actual Y action is used. -/
theorem smul_val (a : F) (v : fixedSpace) :
    (a • v).val = (scalarFieldEquiv a).re • v.val +
      (scalarFieldEquiv a).im • quotientModTwoRepresentation y v.val := rfl

/-- The source's binary dimension bound is at most six over its scalar field. -/
theorem fixedSpace_finrank_le_six : Module.finrank F fixedSpace ≤ 6 := by
  have hc : Nat.card F = 4 := GaloisField.card 2 2 (by decide)
  have he : 4 ^ Module.finrank F fixedSpace = 2 ^ Module.finrank Bit fixedSpace := by
    rw [← hc, ← Module.natCard_eq_pow_finrank (K := F),
      Module.natCard_eq_pow_finrank (K := Bit), Nat.card_zmod]
  have hp : 2 ^ (2 * Module.finrank F fixedSpace) ≤ 2 ^ 12 := by
    rw [pow_mul, show (2 : ℕ)^2 = 4 by decide, he]
    exact Nat.pow_le_pow_right (by decide) fixedSpace_finrank_le_twelve
  have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  omega

/-- Every member of the literal tetrahedral centralizer acts linearly over F. -/
def centralizerAction : centralizerI →* (fixedSpace ≃ₗ[F] fixedSpace) where
  toFun g :=
    { toFun := fun v => ⟨quotientModTwoRepresentation g.val v.val,
        centralizerI_preserves_fixedSpace g.property v.property⟩
      invFun := fun v => ⟨quotientModTwoRepresentation g.val⁻¹ v.val,
        centralizerI_preserves_fixedSpace (centralizerI.inv_mem g.property) v.property⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp
      map_add' := by intro v w; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by
        intro a v
        apply Subtype.ext
        change quotientModTwoRepresentation g.val (a • v).val =
          (a • (⟨quotientModTwoRepresentation g.val v.val,
            centralizerI_preserves_fixedSpace g.property v.property⟩ : fixedSpace)).val
        rw [smul_val, smul_val, map_add, map_smul, map_smul]
        congr 1
        have hc : y * g.val = g.val * y := g.property y ⟨threeCycle, rfl⟩
        have he := congrArg (fun k => quotientModTwoRepresentation k v.val) hc
        exact congrArg (fun w => (scalarFieldEquiv a).im • w) (by
          simpa only [map_mul, LinearEquiv.mul_apply] using he.symm) }
  map_one' := by ext v; exact congrArg (fun f => f v.val) (map_one quotientModTwoRepresentation)
  map_mul' := by
    intro g h
    ext v
    exact congrArg (fun f => f v.val) (map_mul quotientModTwoRepresentation g.val h.val)

@[simp] theorem centralizerAction_apply (g : centralizerI) (v : fixedSpace) :
    (centralizerAction g v).val = quotientModTwoRepresentation g.val v.val := rfl

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
