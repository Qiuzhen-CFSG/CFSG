/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalClassOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalClassTransitivity
public import Theory.AtlasPort.OtherSporadic.Conway.FirstShapeFullStabilizer

/-!
Orbit classification of minimum classes orthogonal to a marked norm-four vector.
The proof combines the concrete support and sign transports for each class profile.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalClassOrbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimumPairMinus_dot (i j : Omega) (x : IntegerCoordinates) :
    integerDot (minimumPairMinus i j).val x = 4 * (x i - x j) := by
  simp [minimumPairMinus,integerDot,coordinateVector,Pi.single_apply,sub_mul,ite_mul,
    Finset.sum_sub_distrib,mul_sub]

theorem monomial_point_minus_image (i j : Omega) (hij : i ≠ j)
    (r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j)) :
    r.val.val.val (minimumPairMinus i j) = minimumPairMinus i j ∨
      r.val.val.val (minimumPairMinus i j) = -minimumPairMinus i j := by
  let s := vectorStabilizerInclusion monomialSubgroup firstShapeStabilizer
    monomial_le_firstShapeStabilizer (minimumPairPlus i j) r
  have hx := firstShape_point_orbit_mem i j hij _ (MulAction.mem_orbit _ s)
  rcases four_orthogonal_partition i j hij _ hx.1 hx.2 with hp | hz
  · exact hp
  · exact (firstShape_no_disjoint_fusion i j hij s hz).elim

theorem monomial_point_zero_iff (i j : Omega) (hij : i ≠ j)
    (r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j)) (x : leech)
    (hx : integerDot (minimumPairPlus i j).val x.val = 0) :
    (r.val.val.val x).val i = 0 ↔ x.val i = 0 := by
  have hy := r.val.val.prop (minimumPairPlus i j) x
  rw [leechVectorStabilizer_fixes] at hy
  have he := r.val.val.prop (minimumPairMinus i j) x
  rw [minimumPairPlus_dot,minimumPairPlus_dot] at hy
  rw [minimumPairPlus_dot] at hx
  rcases monomial_point_minus_image i j hij r with hp | hp
  · rw [hp,minimumPairMinus_dot,minimumPairMinus_dot] at he
    omega
  · rw [hp] at he
    have hneg : integerDot (-minimumPairMinus i j).val (r.val.val.val x).val =
        -integerDot (minimumPairMinus i j).val (r.val.val.val x).val := by
      simp [integerDot,Finset.sum_neg_distrib]
    rw [hneg,minimumPairMinus_dot,minimumPairMinus_dot] at he
    omega

theorem monomial_twoFour_iff (m : GolayMonomialGroup) (x : leech) (k u : ℕ) :
    ((monomialEmbedding m).val x).val ∈ twoFourFamily k u ↔ x.val ∈ twoFourFamily k u := by
  refine ⟨fun h => ?_,monomial_twoFour_invariant m x k u⟩
  have hh := monomial_twoFour_invariant m⁻¹ ((monomialEmbedding m).val x) k u h
  rw [map_inv] at hh
  change (((monomialEmbedding m).val.symm ((monomialEmbedding m).val x))).val ∈ twoFourFamily k u at hh
  simpa only [LinearEquiv.symm_apply_apply] using hh

theorem orthogonalClassIndex_invariant (i j : Omega) (hij : i ≠ j)
    (r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j)) (x : leech)
    (hx : integerDot (minimumPairPlus i j).val x.val = 0) :
    orthogonalClassIndex i (r.val.val.val x) = orthogonalClassIndex i x := by
  obtain ⟨m,hm⟩ := r.val.prop
  have h0 : (r.val.val.val x).val ∈ twoFourFamily 0 2 ↔ x.val ∈ twoFourFamily 0 2 := by
    rw [← hm]; exact monomial_twoFour_iff m x 0 2
  have h1 : (r.val.val.val x).val ∈ twoFourFamily 8 0 ↔ x.val ∈ twoFourFamily 8 0 := by
    rw [← hm]; exact monomial_twoFour_iff m x 8 0
  simp only [orthogonalClassIndex,h0,h1,monomial_point_zero_iff i j hij r x hx]

theorem orthogonalClass_monomial_orbit (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) (y : leech) :
    y ∈ MulAction.orbit (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j))
      (orthogonalClassValue i j t x) ↔
      ∃ z : OrthogonalClassType i j t, orthogonalClassValue i j t z = y := by
  constructor
  · rintro hy
    obtain ⟨r,hr⟩ := MulAction.mem_orbit_iff.mp hy
    have hg := orthogonalClass_good i j hij t x
    have hn := r.val.val.prop (orthogonalClassValue i j t x) (orthogonalClassValue i j t x)
    change integerDot (r.val.val.val _).val (r.val.val.val _).val = _ at hn
    change r.val.val.val (orthogonalClassValue i j t x) = y at hr
    rw [hr,hg.1] at hn
    have ho := r.val.val.prop (minimumPairPlus i j) (orthogonalClassValue i j t x)
    rw [leechVectorStabilizer_fixes,hr,hg.2] at ho
    obtain ⟨s,z,hz⟩ := orthogonalClass_exhaustive i j hij y hn ho
    have ht := orthogonalClassIndex_invariant i j hij r _ hg.2
    rw [hr,← hz,orthogonalClassIndex_value i j hij,
      orthogonalClassIndex_value i j hij] at ht
    subst s
    exact ⟨z,hz⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨r,hr⟩ := orthogonalClass_transitive i j hij t x z
    exact MulAction.mem_orbit_iff.mpr ⟨r,hr⟩

theorem orthogonalClass_monomial_orbit_card (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x : OrthogonalClassType i j t) :
    Nat.card (MulAction.orbit (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j))
      (orthogonalClassValue i j t x)) = ![2,924,42240,4928,45056] t := by
  let f : OrthogonalClassType i j t →
      MulAction.orbit (leechVectorStabilizer monomialSubgroup (minimumPairPlus i j))
        (orthogonalClassValue i j t x) := fun z =>
    ⟨orthogonalClassValue i j t z,(orthogonalClass_monomial_orbit i j hij t x _).mpr ⟨z,rfl⟩⟩
  have hf : Function.Bijective f := ⟨fun a b h => orthogonalClassValue_injective i j t
    (congrArg Subtype.val h),fun y => by
      obtain ⟨z,hz⟩ := (orthogonalClass_monomial_orbit i j hij t x y.val).mp y.prop
      exact ⟨z,Subtype.ext hz⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact orthogonalClass_card i j hij t

end Atlas.Conway
