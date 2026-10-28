module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient
public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineCodeCriterion

/-!
# A concrete square root of the central Leech sign

A hexacode translation interchanges two pairs in each of the six tetrads.
The chosen Golay word changes sign on exactly one point of each pair. Hence
the signed permutation squares to scalar negation on the actual Leech lattice.
Its image in the central quotient is an involution, and both lifts of that
image have order four.

This supplies a coordinate square calculation for the route in
Aschbacher–Smith I.2.2(5), printed p.411, citing Aschbacher (1994), 46.9 and
49.5. Identifying this element with the source root-four class and embedding
the marked octonion G₂(4) group remain separate geometric obligations.
The proof does not infer that identification from the order of the element.

The imported Golay and Leech constructions are the attributed ATLAS ports;
no new upstream source is copied in this module.
-/

@[expose] public section

open Atlas.Codes Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour

def translateWord : hexacode :=
  ⟨hexEncoder (![1, 1, 1], ![0, 0], 0), ⟨_, rfl⟩⟩
def signHexWord : hexacode :=
  ⟨hexEncoder (![0, 0, 0], ![1, 0], 1), ⟨_, rfl⟩⟩
def signWord : golay :=
  ⟨golayEncoder (signHexWord, 0, 0), ⟨_, rfl⟩⟩
def coordinateSwap : Mathieu24CodeModel :=
  ⟨affinePermutation translateWord.val 1,
    affine_preserves_code _ _ translateWord.property (Subgroup.one_mem _)⟩

theorem coordinateSwap_sq (i : Omega) :
    coordinateSwap.val.symm (coordinateSwap.val.symm i) = i := by
  revert i
  decide

theorem signs_opposite (i : Omega) :
    signWord.val (coordinateSwap.val.symm i) = signWord.val i + 1 := by
  revert i
  decide

noncomputable def markedLift : LeechIsometryGroup :=
  signIsometry signWord * permutationIsometry coordinateSwap

theorem markedLift_apply (x : leech) (i : Omega) :
    (markedLift.val x).val i =
      if signWord.val i = 0 then x.val (coordinateSwap.val.symm i)
      else -x.val (coordinateSwap.val.symm i) := rfl

theorem markedLift_sq : markedLift ^ 2 = negationIsometry := by
  rw [pow_two]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  ext i
  change (markedLift.val (markedLift.val x)).val i = (negationIsometry.val x).val i
  rw [markedLift_apply, markedLift_apply, negationIsometry_apply, signs_opposite,
    coordinateSwap_sq]
  rcases bit_cases (signWord.val i) with h | h <;> simp [h]

theorem order_four_of_sq_negation {g : LeechIsometryGroup}
    (hg : g ^ 2 = negationIsometry) : orderOf g = 4 := by
  have h4 : g ^ 4 = 1 := by
    calc
      g ^ 4 = (g ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hg, pow_two, negationIsometry_sq]
  have hd := orderOf_dvd_of_pow_eq_one h4
  have h2 : ¬orderOf g ∣ 2 := by
    intro h
    exact negationIsometry_ne_one (hg.symm.trans (orderOf_dvd_iff_pow_eq_one.mp h))
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  interval_cases hn : orderOf g <;> simp_all

theorem markedLift_order : orderOf markedLift = 4 :=
  order_four_of_sq_negation markedLift_sq

/-- The marked element in the actual quotient of the Leech isometry group. -/
noncomputable def markedInvolution : LeechCentralQuotient :=
  leechCentralProjection markedLift

theorem projection_negation : leechCentralProjection negationIsometry = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [leechCentralProjection_kernel]
  exact (leechCentralSigns_mem _).mpr (Or.inr rfl)

theorem markedInvolution_sq : markedInvolution ^ 2 = 1 := by
  rw [markedInvolution, ← map_pow, markedLift_sq, projection_negation]

/-- Equal images differ by precisely one of the two actual central signs. -/
theorem eq_or_mul_negation_of_projection_eq {x y : LeechIsometryGroup}
    (h : leechCentralProjection x = leechCentralProjection y) :
    x = y ∨ x = y * negationIsometry := by
  have hm := (leechCentralProjection.eq_iff).mp h
  rw [leechCentralProjection_kernel, leechCentralSigns_mem] at hm
  rcases hm with h | h
  · exact Or.inl (inv_mul_eq_one.mp h).symm
  · exact Or.inr ((inv_mul_eq_iff_eq_mul).mp h)

theorem square_eq_of_projection_eq {x y : LeechIsometryGroup}
    (h : leechCentralProjection x = leechCentralProjection y) : x ^ 2 = y ^ 2 := by
  rcases eq_or_mul_negation_of_projection_eq h with rfl | rfl
  · rfl
  · have hc : Commute y negationIsometry :=
      (Subgroup.mem_center_iff.mp negation_mem_center y)
    rw [hc.mul_pow, pow_two negationIsometry, negationIsometry_sq, mul_one]

theorem markedInvolution_ne_one : markedInvolution ≠ 1 := by
  intro h
  have hs := square_eq_of_projection_eq
    (x := markedLift) (y := 1) (h.trans (map_one leechCentralProjection).symm)
  rw [markedLift_sq, one_pow] at hs
  exact negationIsometry_ne_one hs

theorem markedInvolution_order : orderOf markedInvolution = 2 :=
  orderOf_eq_prime markedInvolution_sq markedInvolution_ne_one

theorem lift_sq_of_projection_eq_marked {g : LeechIsometryGroup}
    (hg : leechCentralProjection g = markedInvolution) : g ^ 2 = negationIsometry :=
  (square_eq_of_projection_eq hg).trans markedLift_sq

theorem lift_order_of_projection_eq_marked {g : LeechIsometryGroup}
    (hg : leechCentralProjection g = markedInvolution) : orderOf g = 4 :=
  order_four_of_sq_negation (lift_sq_of_projection_eq_marked hg)

/-- The marked involution cannot lie in either source class represented by
a Golay sign (octad or dodecad). Exhaustion of Conway involution classes is
not asserted here. -/
theorem marked_not_conjugate_sign (c : golay) :
    ¬ IsConj (leechCentralProjection (signIsometry c)) markedInvolution := by
  rintro h
  obtain ⟨a, ha⟩ := isConj_iff.mp h
  obtain ⟨b, rfl⟩ := leechCentralProjection_surjective a
  have hp : leechCentralProjection (MulAut.conj b (signIsometry c)) =
      markedInvolution := by
    simpa only [MulAut.conj_apply, map_mul, map_inv] using ha
  have hs : (signIsometry c) ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact signChange_involutive c.val x.val
  have hsq := lift_sq_of_projection_eq_marked hp
  rw [← map_pow, hs, map_one] at hsq
  exact negationIsometry_ne_one hsq.symm

end Atlas.G2.ConwayRootFour
