module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.Frame

/-!
# Reducing negative-square kernel lifts to positive-square geometry

An isometry centralizing the literal tetrahedral group projectively commutes
with a lift of some nonidentity element of its Klein four subgroup U. Indeed,
if it anticommutes with two independent lifts, it commutes with their product.
All three lifts square to central negation by the checked icosian scalar result.

For a negative-square kernel lift h, choose such a commuting scalar a. Then ha
squares to one and fixes the U-fixed binary space. Once this space has dimension
twelve, it equals the binary fixed space of a. The short-vector uniqueness
bound excludes short signed displacements of ha. A U-fixed cross places ha in
the monomial group, where the independent positive-square displacement result
forces ha to be a central sign. Thus the projective image of h lies in both U
and C(I), whose intersection is trivial, a contradiction.

The final application uses precisely the existing `LongFrame` and
`MonomialShortDisplacement` inputs. Both remain explicit here; the unconditional
negative-square exclusion must await their construction. No root-four marking,
G₂ embedding, conjugacy of scalar models, or centralizer identification is used.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, printed
pp.283–284, and the scalar geometry of Section 48, p.269. The literal Leech
and icosian models are the existing attributed ATLAS ports. This is an
independent lattice-kernel reduction for that construction, not a claim that
the book separately states the negative-square lemma.
-/

public section

open Atlas.Conway Atlas.Codes Atlas.Lattices
open Atlas.G2.ConwayRootFour
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.NegativeSquare

private theorem U_pair : ∃ a b : U, a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 := by
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv
    (G₁ := Multiplicative (ZMod 2 × ZMod 2)) (G₂ := U)
  let a : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (1, 0)
  let b : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (0, 1)
  refine ⟨e a, e b, ?_, ?_, ?_⟩
  · simpa only [map_ne_one_iff e e.injective] using (by decide : a ≠ 1)
  · simpa only [map_ne_one_iff e e.injective] using (by decide : b ≠ 1)
  · rw [← map_mul, map_ne_one_iff e e.injective]
    decide

theorem square_negation_of_U {a : LeechIsometryGroup}
    (ha : leechCentralProjection a ∈ U) (hne : leechCentralProjection a ≠ 1) :
    a ^ 2 = negationIsometry := by
  obtain ⟨b, hb, hb2⟩ := LocalGenerators.U_involution_lift ⟨_, ha⟩ hne
  exact (square_eq_of_projection_eq hb.symm).trans hb2

theorem exists_commuting_U_lift (h : LeechIsometryGroup)
    (hh : leechCentralProjection h ∈ centralizerI) :
    ∃ a : LeechIsometryGroup, leechCentralProjection a ∈ U ∧
      leechCentralProjection a ≠ 1 ∧ a ^ 2 = negationIsometry ∧ Commute h a := by
  obtain ⟨u, v, hu, hv, huv⟩ := U_pair
  have hu' : u.val ≠ 1 := fun he => hu (Subtype.ext he)
  have hv' : v.val ≠ 1 := fun he => hv (Subtype.ext he)
  have huv' : (u.val * v.val) ≠ 1 := fun he => huv (Subtype.ext he)
  obtain ⟨a, ha, ha2⟩ := LocalGenerators.U_involution_lift u hu'
  obtain ⟨b, hb, hb2⟩ := LocalGenerators.U_involution_lift v hv'
  have commutator_sign (c : LeechIsometryGroup) (hc : leechCentralProjection c ∈ U) :
      h * c = c * h ∨ h * c = (c * h) * negationIsometry := by
    apply eq_or_mul_negation_of_projection_eq
    simpa only [map_mul] using (hh _ (U_le_I hc)).symm
  have haU : leechCentralProjection a ∈ U := ha ▸ u.property
  have hbU : leechCentralProjection b ∈ U := hb ▸ v.property
  rcases commutator_sign a haU with hac | hac
  · exact ⟨a, haU, ha ▸ hu', ha2, hac⟩
  rcases commutator_sign b hbU with hbc | hbc
  · exact ⟨b, hbU, hb ▸ hv', hb2, hbc⟩
  have habU : leechCentralProjection (a * b) ∈ U := by
    rw [map_mul]
    exact U.mul_mem haU hbU
  have habne : leechCentralProjection (a * b) ≠ 1 := by
    rw [map_mul, ha, hb]
    exact huv'
  refine ⟨a * b, habU, habne, square_negation_of_U habU habne, ?_⟩
  have hzb : negationIsometry * b = b * negationIsometry :=
    (Subgroup.mem_center_iff.mp negation_mem_center b).symm
  change h * (a * b) = (a * b) * h
  calc
    h * (a * b) = ((a * h) * negationIsometry) * b := by
      rw [← mul_assoc, hac]
    _ = a * (h * b) * negationIsometry := by
      rw [mul_assoc (a * h), hzb]
      group
    _ = (a * b) * h * (negationIsometry * negationIsometry) := by
      rw [hbc]
      group
    _ = (a * b) * h := by rw [negationIsometry_sq, mul_one]

open LocalGenerators PositiveSquare

theorem fixedSpace_eq_scalar_kernel (hw : ScalarFixedSpaceWitness)
    (a : LeechIsometryGroup) (ha : a ^ 2 = negationIsometry)
    (haU : leechCentralProjection a ∈ U) :
    fixedSpace = LinearMap.ker (difference (leechCentralProjection a)) := by
  have hle (b : LeechIsometryGroup) (hb : leechCentralProjection b ∈ U) :
      fixedSpace ≤ LinearMap.ker (difference (leechCentralProjection b)) := by
    intro v hv
    rw [LinearMap.mem_ker]
    change quotientModTwoRepresentation (leechCentralProjection b) v - v = 0
    rw [hv _ hb, sub_self]
  obtain ⟨b, hb, hbU, hbfix⟩ := hw
  have hbspace : fixedSpace = LinearMap.ker (difference (leechCentralProjection b)) := by
    apply le_antisymm (hle b hbU)
    intro v hv
    apply hbfix v
    exact sub_eq_zero.mp hv
  apply Submodule.eq_of_le_of_finrank_eq (hle a haU)
  rw [hbspace, difference_ker_finrank b hb, difference_ker_finrank a ha]

private theorem modTwo_neg (v : LeechModTwo) : -v = v := by
  have hz : (2 : Bit) = 0 := by decide
  have he : v + v = 0 := by
    simpa only [two_smul, zero_smul] using congrArg (fun c : Bit => c • v) hz
  exact (eq_neg_of_add_eq_zero_left he).symm

private theorem difference_fixed (a k : LeechIsometryGroup)
    (ha : a ^ 2 = negationIsometry) (hc : Commute a k)
    (hk : ∀ v : LeechModTwo, leechModTwoRepresentation a v = v →
      leechModTwoRepresentation k v = v) (v : LeechModTwo) :
    leechModTwoRepresentation a (leechModTwoRepresentation k v - v) =
      leechModTwoRepresentation k v - v := by
  let ρ := leechModTwoRepresentation
  have ha2 (w : LeechModTwo) : ρ a (ρ a w) = w := by
    have he : ρ a * ρ a = 1 := by
      rw [← map_mul, ← pow_two, ha, negation_modTwo_trivial]
    exact congrArg (fun f : LeechModTwo ≃ₗ[Bit] LeechModTwo => f w) he
  have hcomm (w : LeechModTwo) : ρ a (ρ k w) = ρ k (ρ a w) := by
    exact congrArg (fun f : LeechModTwo ≃ₗ[Bit] LeechModTwo => f w) (hc.map ρ).eq
  have hs : ρ k (ρ a v + v) = ρ a v + v := hk _ (by
    rw [map_add, ha2, add_comm])
  have hd : ρ a (ρ k v) + ρ k v = ρ a v + v := by
    rw [hcomm]
    exact (map_add (ρ k) (ρ a v) v).symm.trans hs
  have he : (ρ a (ρ k v) - ρ a v) + (ρ k v - v) = 0 := by
    calc
      _ = (ρ a (ρ k v) + ρ k v) - (ρ a v + v) := by abel
      _ = 0 := sub_eq_zero.mpr hd
  rw [map_sub]
  exact (eq_neg_of_add_eq_zero_left he).trans (modTwo_neg _)

/-- Integral scalar commutation is sufficient; no centralizer identification is used. -/
theorem not_shortDisplacement_of_commuting_scalar
    (a k : LeechIsometryGroup) (ha : a ^ 2 = negationIsometry) (hc : Commute a k)
    (hk : ∀ v : LeechModTwo, leechModTwoRepresentation a v = v →
      leechModTwoRepresentation k v = v) : ¬ ShortDisplacement k := by
  have hf (x : leech) := difference_fixed a k ha hc hk (leechReduction x)
  rintro ⟨x, hx | hx⟩
  · have hr : leechReduction (k.val x - x) =
        leechModTwoRepresentation k (leechReduction x) - leechReduction x := by
      rw [map_sub, leechModTwoRepresentation_reduce]
    have hz := short_fixed_eq_zero a ha (k.val x - x) (by rw [hr]; exact hf x) hx.2
    simpa only [hz, leechHalfNorm, integerDot, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Int.zero_ediv, lt_self_iff_false] using hx.1
  · have hr : leechReduction (k.val x + x) =
        leechModTwoRepresentation k (leechReduction x) - leechReduction x := by
      rw [map_add, leechModTwoRepresentation_reduce, sub_eq_add_neg, modTwo_neg]
    have hz := short_fixed_eq_zero a ha (k.val x + x) (by rw [hr]; exact hf x) hx.2
    simpa only [hz, leechHalfNorm, integerDot, ZeroMemClass.coe_zero,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Int.zero_ediv, lt_self_iff_false] using hx.1

/-- Multiplying a negative-square kernel lift by a suitable U-scalar reduces
it to the existing positive-square monomial calculation. -/
theorem negative_square_kernel_of_geometry
    (hw : ScalarFixedSpaceWitness) (hmono : MonomialShortDisplacement)
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = negationIsometry) : False := by
  obtain ⟨a, haU, hane, ha2, hca⟩ := exists_commuting_U_lift h hh
  have heq := fixedSpace_eq_scalar_kernel hw a ha2 haU
  have hspace (v : LeechModTwo) (hv : leechModTwoRepresentation a v = v) :
      v ∈ fixedSpace := by
    rw [heq, LinearMap.mem_ker]
    change leechModTwoRepresentation a v - v = 0
    rw [hv, sub_self]
  let k := h * a
  have hkfix (v : LeechModTwo) (hv : v ∈ fixedSpace) :
      leechModTwoRepresentation k v = v := by
    change leechModTwoRepresentation (h * a) v = v
    rw [map_mul]
    change leechModTwoRepresentation h (leechModTwoRepresentation a v) = v
    have hav : leechModTwoRepresentation a v = v := hv _ haU
    rw [hav, hfix v hv]
  have hk2 : k ^ 2 = 1 := by
    rw [hca.mul_pow, hsq, ha2, negationIsometry_sq]
  have hka : Commute a k := hca.symm.mul_right (Commute.refl a)
  obtain ⟨X, hX⟩ := exists_fixedCross
  have hk : k = 1 ∨ k = negationIsometry :=
    eq_sign_of_fixed_cross hmono k hk2 X (Subtype.ext (hkfix X.val hX))
      (not_shortDisplacement_of_commuting_scalar a k ha2 hka
        (fun v hv => hkfix v (hspace v hv)))
  have hkproj : leechCentralProjection k = 1 := by
    rcases hk with hk | hk
    · rw [hk, map_one]
    · rw [hk, projection_negation]
  have he : leechCentralProjection h = leechCentralProjection a := by
    have haone : leechCentralProjection a * leechCentralProjection a = 1 := by
      rw [← map_mul, ← pow_two, ha2, projection_negation]
    have hkone : leechCentralProjection h * leechCentralProjection a = 1 := by
      simpa only [k, map_mul] using hkproj
    exact mul_right_cancel (hkone.trans haone.symm)
  have hone := eq_one_of_mem_centralizerI_of_mem_I hh (he ▸ U_le_I haU)
  exact hane (he.symm.trans hone)

/-- The already assigned long-frame and monomial geometry discharge every
extra premise of the negative-square exclusion. -/
theorem negative_square_kernel_of_longFrame
    (L : LocalGenerators.LongFrame) (hmono : MonomialShortDisplacement)
    (h : LeechIsometryGroup) (hh : leechCentralProjection h ∈ centralizerI)
    (hfix : ∀ v ∈ fixedSpace, leechModTwoRepresentation h v = v)
    (hsq : h ^ 2 = negationIsometry) : False :=
  negative_square_kernel_of_geometry (scalarFixedSpaceWitness_of_longFrame L)
    hmono h hh hfix hsq

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.NegativeSquare
