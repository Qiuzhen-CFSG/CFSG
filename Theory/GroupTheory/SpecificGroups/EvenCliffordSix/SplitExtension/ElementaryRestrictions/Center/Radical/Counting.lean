module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Radical.Coordinates

/-!
# Counting the normalized radical centralizer

An actor exchanging the first pair cannot centralize its monomial: its signed
correction is one, whereas a vector fixed by that actor has equal entries on
the pair. Thus only the four actors on the remaining letters occur.

For each actor, subtracting one chosen solution injects the mixed vector fiber
into its homogeneous fiber. The checked homogeneous count is 24, and the two
independent signs give the bound 48. This uses the original square condition,
signed commutation, and mixed vector equation.

Source: Aschbacher–Smith, I.2.2(6a), printed pp.410 and 412, the split-extension
calculation for the quartic radical.
-/

@[expose] public section
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions.Radical
open Equiv

private theorem cocycle_pair_left (v : V) :
    cocycle Structure.leftA.vector.val v.val = v.val 0 := by
  simp [cocycle, Structure.leftA, Fin.sum_univ_succ]

private theorem cocycle_pair_right (v : V) :
    cocycle v.val Structure.leftA.vector.val = v.val 1 := by
  have h (i : Fin 6) : Finset.Ioi i = Finset.univ.filter (i < ·) := by ext j; simp
  simp only [cocycle, h, Finset.sum_filter]
  simp [Structure.leftA, Fin.sum_univ_succ]
  ring_nf
  simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]

/-- Signed commutation rules out the actors which exchange the first pair. -/
private theorem canonical_actor (x : SplitExtension) (hx : x ^ 2 ∈ sign)
    (hc : Commute (radicalEmbedding Structure.leftA) x) :
    ∃ i : Fin 4, x.right.val = pairActor i := by
  obtain ⟨hsq, hfix⟩ := (square_mem_sign_iff x).mp hx
  have hp : permuteVector x.right.val Structure.leftA.vector = Structure.leftA.vector := by
    have h := congrArg (fun z : SplitExtension => z.left.vector) hc.eq
    change Structure.leftA.vector + x.left.vector =
      x.left.vector + permuteVector x.right.val Structure.leftA.vector at h
    rw [add_comm Structure.leftA.vector] at h
    exact (add_left_cancel h).symm
  rcases pair_actor_cases x.right hsq hp with h | ⟨h0, hsign⟩
  · exact h
  · have hw : x.left.vector.val 0 = x.left.vector.val 1 := by
      have h := congrArg (fun v : V => v.val (x.right.val 0)) hfix
      change x.left.vector.val (x.right.val.symm (x.right.val 0)) =
        x.left.vector.val (x.right.val 0) at h
      rw [(x.right.val).symm_apply_apply 0, h0] at h
      exact h
    have h := ((commute_iff_coordinates (radicalEmbedding Structure.leftA) x).mp hc).2.2
    change signedCorrection 1 x.left.vector +
        cocycle Structure.leftA.vector.val (permuteVector 1 x.left.vector).val =
      signedCorrection x.right.val Structure.leftA.vector +
        cocycle x.left.vector.val (permuteVector x.right.val Structure.leftA.vector).val at h
    rw [show permuteVector 1 x.left.vector = x.left.vector from rfl,
      signedCorrection_one, zero_add, hp, cocycle_pair_left, cocycle_pair_right,
      hsign, hw] at h
    have he : (0 : F) = 1 := add_right_cancel (by simpa only [zero_add] using h)
    exact (zero_ne_one he).elim

/-- Translation within each nonempty vector fiber preserves its actor and
injects it into the corresponding homogeneous fiber. -/
private theorem affine_card_le (i : Fin 4) (u : V) :
    Nat.card (vectorFibers i u) ≤ Nat.card (vectorFibers i 0) := by
  classical
  let P (j : Fin 4) (w : V) := permuteVector (pairActor j) w = w ∧
    u + permuteVector (pairActor i) w = w + permuteVector (pairActor j) u
  let base (j : Fin 4) : V := if h : ∃ w, P j w then h.choose else 0
  have hb (j : Fin 4) (h : ∃ w, P j w) : P j (base j) := by
    simp only [base, dif_pos h]
    exact h.choose_spec
  have translate (q : vectorFibers i u) :
      permuteVector (pairActor q.val.1) (q.val.2 - base q.val.1) = q.val.2 - base q.val.1 ∧
      (0 : V) + permuteVector (pairActor i) (q.val.2 - base q.val.1) =
        q.val.2 - base q.val.1 + permuteVector (pairActor q.val.1) 0 := by
    have hbase := hb q.val.1 ⟨q.val.2, q.property⟩
    constructor
    · rw [permuteVector_eq, map_sub]
      exact congrArg₂ (· - ·) q.property.1 hbase.1
    · have h := congrArg₂ (· - ·) q.property.2 hbase.2
      simp only [add_sub_add_left_eq_sub, add_sub_add_right_eq_sub] at h
      simpa only [permuteVector_eq, map_sub, map_zero, zero_add, add_zero] using h
  let f (q : vectorFibers i u) : vectorFibers i 0 :=
    ⟨(q.val.1, q.val.2 - base q.val.1), translate q⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  have hfst : a.val.1 = b.val.1 := congrArg (fun q : vectorFibers i 0 => q.val.1) hab
  have hsnd : a.val.2 - base a.val.1 = b.val.2 - base b.val.1 :=
    congrArg (fun q : vectorFibers i 0 => q.val.2) hab
  rw [hfst] at hsnd
  exact Subtype.ext (Prod.ext hfst (sub_left_injective hsnd))

/-- The affine mixed equations admit at most 24 actor-vector pairs. -/
private theorem vectorFibers_card_le (i : Fin 4) (hi : i ≠ 0) (u : V) :
    Nat.card (vectorFibers i u) ≤ 24 := by
  calc
    Nat.card (vectorFibers i u) ≤ Nat.card (vectorFibers i 0) := affine_card_le i u
    _ = 24 := homogeneous_card i hi

/-- A nonidentity actor cuts the normalized radical centralizer down to at
most 48 mixed candidates, including their independent signs. -/
theorem canonical_card_le (x : SplitExtension) (hx : x ^ 2 ∈ sign)
    (hr : x.right ≠ 1) (hc : Commute (radicalEmbedding Structure.leftA) x) :
    Nat.card (mixedCandidates Structure.leftA x) ≤ 48 := by
  classical
  obtain ⟨i, hi⟩ := canonical_actor x hx hc
  have hi0 : i ≠ 0 := by
    intro h
    apply hr
    apply Subtype.ext
    rw [hi, h]
    rfl
  let index (y : mixedCandidates Structure.leftA x) : Fin 4 :=
    (canonical_actor y.val y.property.1 y.property.2.1).choose
  have hindex (y : mixedCandidates Structure.leftA x) : y.val.right.val = pairActor (index y) :=
    (canonical_actor y.val y.property.1 y.property.2.1).choose_spec
  have hvec (y : mixedCandidates Structure.leftA x) :
      permuteVector (pairActor (index y)) y.val.left.vector = y.val.left.vector ∧
      x.left.vector + permuteVector (pairActor i) y.val.left.vector =
        y.val.left.vector + permuteVector (pairActor (index y)) x.left.vector := by
    constructor
    · rw [← hindex y]
      exact ((square_mem_sign_iff y.val).mp y.property.1).2
    · rw [← hi, ← hindex y]
      exact y.property.2.2.2
  let f (y : mixedCandidates Structure.leftA x) : F × vectorFibers i x.left.vector :=
    (y.val.left.sign, ⟨(index y, y.val.left.vector), hvec y⟩)
  have hinj : Function.Injective f := by
    intro a b hab
    have hs : a.val.left.sign = b.val.left.sign := congrArg Prod.fst hab
    have hj : index a = index b := congrArg (fun z : F × vectorFibers i x.left.vector => z.2.val.1) hab
    have hv : a.val.left.vector = b.val.left.vector :=
      congrArg (fun z : F × vectorFibers i x.left.vector => z.2.val.2) hab
    apply Subtype.ext
    apply SemidirectProduct.ext (Model.ext hs hv)
    apply Subtype.ext
    rw [hindex a, hindex b, hj]
  have h := Nat.card_le_card_of_injective f hinj
  have hF : Nat.card F = 2 := by simp [F, Nat.card_eq_fintype_card]
  calc
    Nat.card (mixedCandidates Structure.leftA x) ≤ Nat.card (F × vectorFibers i x.left.vector) := h
    _ = 2 * Nat.card (vectorFibers i x.left.vector) := by rw [Nat.card_prod, hF]
    _ ≤ 2 * 24 := Nat.mul_le_mul_left 2 (vectorFibers_card_le i hi0 x.left.vector)
    _ = 48 := rfl

end EvenCliffordSix.SplitExtension.ElementaryRestrictions.Radical
