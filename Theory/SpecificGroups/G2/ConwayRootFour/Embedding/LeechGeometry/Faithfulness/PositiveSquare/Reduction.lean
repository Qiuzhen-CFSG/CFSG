module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.Kernel
public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossTransitivity

/-!
# Short displacements and the positive-square kernel branch

A negative-square lattice isometry has no nonzero short vector whose reduction
it fixes: uniqueness of short representatives would give a real eigenvector.
If its binary fixed space equals the specified U-fixed space, a kernel element
has no short displacement. A U-fixed cross then conjugates a positive-square
kernel element into the actual monomial group.

The two remaining inputs are kept explicit: the scalar fixed-space identity
and a short-displacement calculation for monomial involutions. Neither input
asserts the desired faithful action or identifies the Conway centralizer.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, printed pp.283–284,
with the scalar geometry of Section 48, p.269. The lattice, quotient, short
representative bound and monomial recovery are the attributed ATLAS ports.
-/

public section

open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.PositiveSquare

/-- A norm below eight occurs among the displacement by h or by -h.
`leechHalfNorm` is half the normalized lattice norm, not the raw coordinate sum. -/
@[expose] def ShortDisplacement (h : LeechIsometryGroup) : Prop :=
  ∃ x : leech,
    (0 < leechHalfNorm (h.val x - x) ∧ leechHalfNorm (h.val x - x) < 4) ∨
    (0 < leechHalfNorm (h.val x + x) ∧ leechHalfNorm (h.val x + x) < 4)

/-- The actual fixed-space identity needed from integral quaternion geometry.
The membership clause ties the scalar to the literal U of `ScalarFour`. -/
@[expose] def ScalarFixedSpaceWitness : Prop :=
  ∃ a : LeechIsometryGroup, a ^ 2 = negationIsometry ∧
    leechCentralProjection a ∈ U ∧
    ∀ v : LeechModTwo, leechModTwoRepresentation a v = v → v ∈ fixedSpace

private theorem modTwo_neg (v : LeechModTwo) : -v = v := by
  have hz : (2 : Bit) = 0 := by decide
  have he : v + v = 0 := by
    simpa only [two_smul, zero_smul] using congrArg (fun c : Bit => c • v) hz
  exact (eq_neg_of_add_eq_zero_left he).symm

private theorem halfNorm_isometry (h : LeechIsometryGroup) (x : leech) :
    leechHalfNorm (h.val x) = leechHalfNorm x := by
  exact congrArg (fun n : ℤ => n / 16) (h.property x x)

/-- A negative-square lift cannot fix the class of a nonzero vector of norm < 8. -/
theorem short_fixed_eq_zero (a : LeechIsometryGroup)
    (ha : a ^ 2 = negationIsometry) (x : leech)
    (hfix : leechModTwoRepresentation a (leechReduction x) = leechReduction x)
    (hn : leechHalfNorm x < 4) : x = 0 := by
  have hsq : a.val (a.val x) = -x := by
    have he := congrArg (fun g : LeechIsometryGroup => g.val x) ha
    simpa only [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply,
      negationIsometry_apply] using he
  have hc : leechReduction (a.val x) = leechReduction x := hfix
  have he := leech_congruent_short_unique (a.val x) x hc (by
    rw [halfNorm_isometry]
    omega)
  have hh : a.val (a.val x) = x := by
    rcases he with he | he
    · rw [he, he]
    · rw [he, map_neg, he, neg_neg]
  have hx : x = -x := hh.symm.trans hsq
  apply Subtype.ext
  ext i
  have hi := congrArg (fun z : leech => z.val i) hx
  change x.val i = -x.val i at hi
  change x.val i = 0
  omega

private theorem displacement_fixed (a h : LeechIsometryGroup)
    (ha : a ^ 2 = negationIsometry) (haU : leechCentralProjection a ∈ U)
    (hspace : ∀ v, leechModTwoRepresentation a v = v → v ∈ fixedSpace)
    (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (v : LeechModTwo) :
    leechModTwoRepresentation a (leechModTwoRepresentation h v - v) =
      leechModTwoRepresentation h v - v := by
  let ρ := leechModTwoRepresentation
  have ha2 : ∀ w, ρ a (ρ a w) = w := by
    intro w
    have he : ρ a * ρ a = 1 := by
      rw [← map_mul, ← pow_two, ha, negation_modTwo_trivial]
    exact congrArg (fun f : LeechModTwo ≃ₗ[Bit] LeechModTwo => f w) he
  have hc : ∀ w, ρ a (ρ h w) = ρ h (ρ a w) := by
    intro w
    have he := congrArg quotientModTwoRepresentation (hh _ (U_le_I haU))
    simp only [map_mul, quotientModTwoRepresentation_compatible] at he
    exact congrArg (fun f : LeechModTwo ≃ₗ[Bit] LeechModTwo => f w) he
  have hs : ρ h (ρ a v + v) = ρ a v + v := hfix _ (hspace _ (by
    rw [map_add, ha2, add_comm]))
  have hd : ρ a (ρ h v) + ρ h v = ρ a v + v := by
    rw [hc]
    exact (map_add (ρ h) (ρ a v) v).symm.trans hs
  have he : (ρ a (ρ h v) - ρ a v) + (ρ h v - v) = 0 := by
    calc
      _ = (ρ a (ρ h v) + ρ h v) - (ρ a v + v) := by abel
      _ = 0 := sub_eq_zero.mpr hd
  rw [map_sub]
  exact (eq_neg_of_add_eq_zero_left he).trans (modTwo_neg _)

/-- Application of the scalar fixed-space identity to the literal kernel:
all short signed displacements are excluded. The square of h is not needed here. -/
theorem not_shortDisplacement_of_scalar (hw : ScalarFixedSpaceWitness)
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v) :
    ¬ ShortDisplacement h := by
  obtain ⟨a, ha, haU, hspace⟩ := hw
  have hf (x : leech) := displacement_fixed a h ha haU hspace hh hfix (leechReduction x)
  rintro ⟨x, hx | hx⟩
  · have hr : leechReduction (h.val x - x) =
        leechModTwoRepresentation h (leechReduction x) - leechReduction x := by
      rw [map_sub, leechModTwoRepresentation_reduce]
    have hz := short_fixed_eq_zero a ha (h.val x - x) (by rw [hr]; exact hf x) hx.2
    simpa only [hz, leechHalfNorm, integerDot, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Int.zero_ediv, lt_self_iff_false] using hx.1
  · have hr : leechReduction (h.val x + x) =
        leechModTwoRepresentation h (leechReduction x) - leechReduction x := by
      rw [map_add, leechModTwoRepresentation_reduce, sub_eq_add_neg, modTwo_neg]
    have hz := short_fixed_eq_zero a ha (h.val x + x) (by rw [hr]; exact hf x) hx.2
    simpa only [hz, leechHalfNorm, integerDot, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Int.zero_ediv, lt_self_iff_false] using hx.1

/-- Short displacement is preserved when changing the lattice frame. -/
theorem shortDisplacement_of_conjugate (h s : LeechIsometryGroup)
    (hs : ShortDisplacement (s⁻¹ * h * s)) : ShortDisplacement h := by
  obtain ⟨x, hx | hx⟩ := hs
  · refine ⟨s.val x, Or.inl ?_⟩
    have he : s.val ((s⁻¹ * h * s).val x - x) = h.val (s.val x) - s.val x := by
      change s.val (s.val.symm (h.val (s.val x)) - x) = _
      rw [map_sub, LinearEquiv.apply_symm_apply]
    have hn := halfNorm_isometry s ((s⁻¹ * h * s).val x - x)
    rw [he] at hn
    rwa [hn]
  · refine ⟨s.val x, Or.inr ?_⟩
    have he : s.val ((s⁻¹ * h * s).val x + x) = h.val (s.val x) + s.val x := by
      change s.val (s.val.symm (h.val (s.val x)) + x) = _
      rw [map_add, LinearEquiv.apply_symm_apply]
    have hn := halfNorm_isometry s ((s⁻¹ * h * s).val x + x)
    rw [he] at hn
    rwa [hn]

/-- The remaining coordinate calculation involves only actual signed permutations. -/
@[expose] def MonomialShortDisplacement : Prop :=
  ∀ m : GolayMonomialGroup, (monomialEmbedding m) ^ 2 = 1 →
    monomialEmbedding m ≠ 1 → monomialEmbedding m ≠ negationIsometry →
    ShortDisplacement (monomialEmbedding m)

/-- Any fixed cross allows the monomial calculation to be applied, without
presuming a root-four marking or a distinguished U-fixed coordinate cross. -/
theorem eq_sign_of_fixed_cross (hmono : MonomialShortDisplacement)
    (h : LeechIsometryGroup) (hsq : h ^ 2 = 1)
    (X : LeechCross) (hX : crossAction h X = X)
    (hshort : ¬ ShortDisplacement h) : h = 1 ∨ h = negationIsometry := by
  let _ := full_cross_transitive
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq LeechIsometryGroup standardCross X
  change crossAction s standardCross = X at hs
  let k := s⁻¹ * h * s
  have hkX : crossAction k standardCross = standardCross := by
    rw [show k = s⁻¹ * (h * s) by dsimp [k]; group]
    rw [crossAction_mul, crossAction_mul, hs, hX, ← hs, ← crossAction_mul,
      inv_mul_cancel]
    rfl
  let m := recoverMonomial k hkX
  have hm : monomialEmbedding m = k := recoverMonomial_spec k hkX
  have hk2 : k ^ 2 = 1 := by
    calc
      k ^ 2 = s⁻¹ * h ^ 2 * s := by dsimp [k]; simp only [pow_two]; group
      _ = 1 := by rw [hsq]; group
  have hkshort : ¬ ShortDisplacement k := fun hk =>
    hshort (shortDisplacement_of_conjugate h s hk)
  have hk : k = 1 ∨ k = negationIsometry := by
    by_contra! hn
    exact hkshort (hm ▸ hmono m (hm ▸ hk2) (hm ▸ hn.1) (hm ▸ hn.2))
  have hrecover : s * k * s⁻¹ = h := by dsimp [k]; group
  rcases hk with hk | hk
  · left
    rw [hk] at hrecover
    simpa using hrecover.symm
  · right
    rw [hk] at hrecover
    have hc : s * negationIsometry = negationIsometry * s :=
      Subgroup.mem_center_iff.mp negation_mem_center s
    rw [hc, mul_assoc, mul_inv_cancel, mul_one] at hrecover
    exact hrecover.symm

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.PositiveSquare
