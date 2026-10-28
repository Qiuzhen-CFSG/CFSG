module
public import Theory.GroupAction.Order512FiveStructure
public import Theory.GroupAction.PrimeOrbitCommutator

/-!
# Generating orbits in Parrott's two-group

For the order-512 two-group with the original order-five action, every
element outside the derived subgroup has an orbit generating the group.
The action on the quotient by the center has trivial fixed subgroup, so
the commutator line of such an element in that quotient cannot have order
two. Frattini nongeneration and the irreducible order-sixteen Frattini
quotient supply generation; coprime fixed-point lifting supplies the
quotient fixed-point assertion.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.672–674, Lemma 1 and property (d).
-/

namespace Theory.GroupAction
open Subgroup

private theorem orbit_closure_invariant
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V] (b : V) :
    IsInvariant A V (closure (Set.range (fun a : A => a • b))) := by
  let S := closure (Set.range (fun a : A => a • b))
  have hforward (a : A) (x : V) (hx : x ∈ S) : a • x ∈ S := by
    refine closure_induction (p := fun x _ => a • x ∈ S) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨c, rfl⟩
      exact subset_closure ⟨a * c, mul_smul a c b⟩
    · simp only [smul_one]; exact S.one_mem
    · intro x y _ _ hx hy
      simpa only [smul_mul'] using S.mul_mem hx hy
    · intro x _ hx
      simpa only [smul_inv'] using S.inv_mem hx
  refine ⟨fun a x => ⟨hforward a x, fun hx => ?_⟩⟩
  simpa only [inv_smul_smul] using hforward a⁻¹ (a • x) hx

/-- The orbit of every element outside the derived group generates the
order-512 group from Parrott's intrinsic hypotheses. -/
public theorem parrott_orbit_closure_eq_top
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 512)
    (hclass : 3 ≤ Group.nilpotencyClass V) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ center V)
    (b : V) (hb : b ∉ commutator V) :
    closure (Set.range (fun a : A => a • b)) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent V := hV.isNilpotent
  obtain ⟨_, _, hPhi, hUpper, _, hDcard⟩ :=
    parrott_twoGroup_structure hV hcard hclass hA hfixed
  have hZPhi : center V ≤ frattini V := by
    rw [← hPhi, hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono V (show 1 ≤ 2 by decide)
  let : MulDistribMulAction A (V ⧸ frattini V) :=
    quotientMulDistribMulAction (frattini V) (isInvariant_of_characteristic (frattini V))
  have hPhi16 : Nat.card (V ⧸ frattini V) = 16 := by
    have hPhicard : Nat.card (frattini V) = 32 := hPhi ▸ hDcard
    have hc := (frattini V).index_mul_card
    change Nat.card (V ⧸ frattini V) * Nat.card (frattini V) = Nat.card V at hc
    rw [hPhicard, hcard] at hc
    omega
  have hPhifixed : FixedPoints.subgroup A (V ⧸ frattini V) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable V) (by rw [hA, hcard]; decide)
      (frattini V) (isInvariant_of_characteristic (frattini V)), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hfixed.trans hZPhi
  let S := closure (Set.range (fun a : A => a • b))
  let : IsInvariant A V S := orbit_closure_invariant b
  rcases invariant_frattini_dichotomy_of_five hA hPhi16 hPhifixed S with hle | htop
  · exact (hb (hPhi.symm ▸ hle (subset_closure ⟨1, one_smul A b⟩))).elim
  · exact frattini_nongenerating htop

/-- In the quotient by the center, an element outside the derived subgroup
cannot have a commutator image of order two. -/
public theorem parrott_center_quotient_commutator_card_ne_two
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 512)
    (hclass : 3 ≤ Group.nilpotencyClass V) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ center V)
    (b : V) (hb : b ∉ commutator V) :
    Nat.card ↥(⁅zpowers (QuotientGroup.mk' (center V) b),
      (⊤ : Subgroup (V ⧸ center V))⁆) ≠ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : Group.IsNilpotent V := hV.isNilpotent
  let : MulDistribMulAction A (V ⧸ center V) :=
    quotientMulDistribMulAction (center V) (isInvariant_of_characteristic (center V))
  have hQfixed : FixedPoints.subgroup A (V ⧸ center V) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable V) (by rw [hA, hcard]; decide)
      (center V) (isInvariant_of_characteristic (center V)), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hfixed
  let q := QuotientGroup.mk' (center V)
  have hgen := parrott_orbit_closure_eq_top hV hcard hclass hA hfixed b hb
  have hgenQ : closure (Set.range (fun a : A => a • q b)) = ⊤ := by
    have hm : (closure (Set.range (fun a : A => a • b))).map q =
        closure (Set.range (fun a : A => a • q b)) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hm
    exact hm.symm
  exact commutator_zpowers_card_ne_two_of_prime_orbit hA hQfixed (q b) hgenQ

end Theory.GroupAction
