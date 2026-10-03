module
public import Theory.SpecificGroups.ReeTwo.FixingModelTwoStructure
public import Theory.SpecificGroups.ReeTwo.FixingModelTwoPowers

/-!
# The fixed mark in the nonsplit fixing base-two first core

The mark has 768 fourth roots in the intrinsic first core, while each other
nonidentity central element has 256. Automorphisms preserve these finite
fibers and the center, forcing them to fix the mark.

Source: Shinoda (1975), pp.81–83, through the verified core coordinates and
the nonsplit cyclic carry model; invariance of power fibers under isomorphisms.
-/

namespace ReeTwo.FixingModel
open Two

private def count (x : Model 2 true) : ℕ := Fintype.card {p : Params // fourthPolynomial (elt true p) = x}

private noncomputable def fourthRootCard (x : firstCore 2 true) : ℕ := Nat.card {y : firstCore 2 true // y ^ 4 = x}

private theorem fourthRootCard_aut (a : MulAut (firstCore 2 true)) (x : firstCore 2 true) :
    fourthRootCard (a x) = fourthRootCard x := by
  symm
  apply Nat.card_congr
  refine a.toEquiv.subtypeEquiv ?_
  intro y
  change y ^ 4 = x ↔ (a y) ^ 4 = a x
  rw [← map_pow, a.injective.eq_iff]

private theorem fourthRootCard_eq (x : firstCore 2 true) : fourthRootCard x = count x.val := by
  unfold fourthRootCard count
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine (parameterEquiv true).subtypeEquiv ?_
  intro y
  rw [fourthPolynomial_eq _ rfl]
  have he : elt true (parameterEquiv true y) = y.val := congrArg Subtype.val ((parameterEquiv true).symm_apply_apply y)
  rw [he]
  exact Subtype.ext_iff

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxSize 4096 in
private theorem counts : count (root true 9) = 768 ∧ count (special true) = 256 ∧
    count (special true * root true 9) = 256 := by
  decide +kernel

/-- The marked element has exactly 768 fourth roots in the nonsplit first core. -/
public theorem two_true_marked_fourth_roots :
    Nat.card {y : firstCore 2 true // y ^ 4 = centralInvolution 2 true} = 768 := by
  change fourthRootCard (centralInvolution 2 true) = 768
  rw [fourthRootCard_eq]
  exact counts.1

/-- Each other nonidentity central element has exactly 256 fourth roots. -/
public theorem two_true_other_fourth_roots (x : firstCore 2 true)
    (hx : x ∈ Subgroup.center (firstCore 2 true))
    (hx1 : x ≠ 1) (hxz : x ≠ centralInvolution 2 true) :
    Nat.card {y : firstCore 2 true // y ^ 4 = x} = 256 := by
  change fourthRootCard x = 256
  rw [fourthRootCard_eq]
  rcases firstCore_center_cases true x hx with h | h | h | h
  · exact False.elim (hx1 (Subtype.ext h))
  · rw [h, counts.2.1]
  · exact False.elim (hxz (Subtype.ext h))
  · rw [h, counts.2.2]

/-- Fourth-root counts distinguish the last root in the fixing action-2 model. -/
public theorem two_true_fixed (a : MulAut (firstCore 2 true)) :
    a (centralInvolution 2 true) = centralInvolution 2 true := by
  have hc : a (centralInvolution 2 true) ∈ Subgroup.center (firstCore 2 true) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a
      (Subgroup.mem_center_iff.mp (centralInvolution_mem_center 2 true) x)
  have hn : a (centralInvolution 2 true) ≠ 1 := by
    intro h
    exact centralInvolution_ne_one 2 true (a.injective (h.trans (map_one a).symm))
  have hcount := fourthRootCard_aut a (centralInvolution 2 true)
  rw [fourthRootCard_eq, fourthRootCard_eq] at hcount
  change count (a (centralInvolution 2 true)).val = count (root true 9) at hcount
  rcases firstCore_center_cases true _ hc with h | h | h | h
  · exact False.elim (hn (Subtype.ext h))
  · rw [h, counts.1, counts.2.1] at hcount
    omega
  · exact Subtype.ext h
  · rw [h, counts.1, counts.2.2] at hcount
    omega


end ReeTwo.FixingModel
