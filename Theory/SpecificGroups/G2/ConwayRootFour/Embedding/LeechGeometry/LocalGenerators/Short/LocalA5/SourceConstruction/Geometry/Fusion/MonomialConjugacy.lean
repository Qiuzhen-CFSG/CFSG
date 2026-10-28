module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialReduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy.SignResolution
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy.MathieuInvolutions

/-!
# Scalar conjugacy for negative-square Leech lifts

For the marked coordinate involution, the Golay calculation in
`SignResolution` constructs a sign isometry conjugating every negative-square
monomial lift to `markedLift`. Conjugating the coordinate permutation first
therefore gives genuine conjugacy in the literal Leech central quotient.
The proved marking of the scalar A₅ identifies this class with
`scalarInvolution`.

The Mathieu involution theorem supplies the coordinate conjugator in the
actual Golay automorphism group. This completes monomial fusion without
additional premises. The odd-cross reduction then extends the result to every
negative-square Leech isometry, using the same literal central quotient.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, using Lemma 47.2, p.261 and the root-four conventions p.269.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

/-- The conjugator is an actual Golay sign isometry of the Leech lattice. -/
theorem monomial_isConj_markedLift_of_right_eq (m : GolayMonomialGroup)
    (hm : (monomialEmbedding m) ^ 2 = negationIsometry)
    (hp : m.right = coordinateSwap) : IsConj (monomialEmbedding m) markedLift := by
  have hc := (monomial_square_negation_parameters m hm).2.1
  rw [hp] at hc
  obtain ⟨b, hb⟩ := opposite_signs_eq_marked_coboundary m.left.toAdd hc
  have he : signIsometry b * monomialEmbedding m = markedLift * signIsometry b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    funext i
    change (if b.val i = 0 then ((monomialEmbedding m).val x).val i
      else -((monomialEmbedding m).val x).val i) =
      (markedLift.val ((signIsometry b).val x)).val i
    rw [monomialEmbedding_apply, hp, markedLift_apply]
    change (if b.val i = 0 then
        (if m.left.toAdd.val i = 0 then x.val (coordinateSwap.val.symm i)
          else -x.val (coordinateSwap.val.symm i))
      else -(if m.left.toAdd.val i = 0 then x.val (coordinateSwap.val.symm i)
          else -x.val (coordinateSwap.val.symm i))) =
      (if signWord.val i = 0 then
        (if b.val (coordinateSwap.val.symm i) = 0 then x.val (coordinateSwap.val.symm i)
          else -x.val (coordinateSwap.val.symm i))
       else -(if b.val (coordinateSwap.val.symm i) = 0 then x.val (coordinateSwap.val.symm i)
          else -x.val (coordinateSwap.val.symm i)))
    have h := hb i
    rcases bit_cases (b.val i) with h₁ | h₁ <;>
      rcases bit_cases (b.val (coordinateSwap.val.symm i)) with h₂ | h₂ <;>
      rcases bit_cases (m.left.toAdd.val i) with h₃ | h₃ <;>
      rcases bit_cases (signWord.val i) with h₄ | h₄ <;> simp_all
  exact isConj_iff.mpr ⟨signIsometry b, by rw [he]; group⟩

/-- Coordinate conjugacy, followed by the proved sign calculation, gives
conjugacy in the literal Leech central quotient. -/
theorem monomial_projection_isConj_scalar_of_coordinate_conjugacy (m : GolayMonomialGroup)
    (hm : (monomialEmbedding m) ^ 2 = negationIsometry)
    (hp : IsConj m.right coordinateSwap) :
    IsConj (leechCentralProjection (monomialEmbedding m)) scalarInvolution := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hp
  let u : GolayMonomialGroup := SemidirectProduct.inr a
  let n := u * m * u⁻¹
  have hn : n.right = coordinateSwap := ha
  have hconj : IsConj (monomialEmbedding m) (monomialEmbedding n) :=
    monomialEmbedding.map_isConj (isConj_iff.mpr ⟨u, rfl⟩)
  have hsq : (monomialEmbedding n) ^ 2 = negationIsometry := by
    change (monomialEmbedding (u * m * u⁻¹)) ^ 2 = _
    rw [map_mul, map_mul, map_inv]
    calc
      (monomialEmbedding u * monomialEmbedding m * (monomialEmbedding u)⁻¹) ^ 2 =
          monomialEmbedding u * (monomialEmbedding m) ^ 2 * (monomialEmbedding u)⁻¹ := by
        simp only [pow_two]
        group
      _ = negationIsometry := by
        rw [hm, Subgroup.mem_center_iff.mp negation_mem_center (monomialEmbedding u)]
        simp [mul_assoc]
  exact (leechCentralProjection.map_isConj
    (hconj.trans (monomial_isConj_markedLift_of_right_eq n hsq hn))).trans
    scalarInvolution_isConj_marked.symm

/-- Remaining assembly input: conjugacy of fixed-point-free involutions in
 the actual Mathieu coordinate group. The sign-lift premise is discharged. -/
theorem monomial_projection_isConj_scalar_of_mathieu
    (hmathieu : ∀ p : Mathieu24CodeModel,
      Function.Involutive p.val.symm → (∀ i, p.val.symm i ≠ i) →
      IsConj p coordinateSwap)
    (m : GolayMonomialGroup) (hm : (monomialEmbedding m) ^ 2 = negationIsometry) :
    IsConj (leechCentralProjection (monomialEmbedding m)) scalarInvolution := by
  obtain ⟨h₂, _, hfree⟩ := monomial_square_negation_parameters m hm
  exact monomial_projection_isConj_scalar_of_coordinate_conjugacy m hm
    (hmathieu m.right h₂ hfree)

/-- Apply the actual odd-cross reduction to arbitrary negative-square lifts.
Only the Mathieu coordinate-conjugacy input remains. -/
theorem projection_isConj_scalar_of_mathieu
    (hmathieu : ∀ p : Mathieu24CodeModel,
      Function.Involutive p.val.symm → (∀ i, p.val.symm i ≠ i) →
      IsConj p coordinateSwap)
    (g : LeechIsometryGroup) (hg : g ^ 2 = negationIsometry) :
    IsConj (leechCentralProjection g) scalarInvolution :=
  projection_isConj_scalar_of_monomial
    (monomial_projection_isConj_scalar_of_mathieu hmathieu) g hg

/-- Every negative-square Golay monomial lift projects to the scalar class.
The Mathieu coordinate conjugator and the Golay sign conjugator are both
constructed in the preceding results. -/
theorem monomial_projection_isConj_scalar (m : GolayMonomialGroup)
    (hm : (monomialEmbedding m) ^ 2 = negationIsometry) :
    IsConj (leechCentralProjection (monomialEmbedding m)) scalarInvolution :=
  monomial_projection_isConj_scalar_of_mathieu
    mathieu_fixedPointFree_involution_isConj_coordinateSwap m hm

/-- The odd-cross reduction now gives scalar conjugacy for every
negative-square Leech lift, with the monomial fusion premise discharged. -/
theorem projection_isConj_scalar_of_square_negation
    (g : LeechIsometryGroup) (hg : g ^ 2 = negationIsometry) :
    IsConj (leechCentralProjection g) scalarInvolution :=
  projection_isConj_scalar_of_monomial monomial_projection_isConj_scalar g hg

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
