module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Reduction
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers

/-!
# Nonradical square-admissible centralizers in the signed extension

A nonidentity involution in A₆ is conjugate to (01)(23). Its fixed even
vectors have the form (a,a,b,b,c,c); conjugation by the Clifford radical
reduces such a vector to zero or the volume vector. The remaining left
coordinate is central, so it does not affect the commuting set.

For the pure double transposition, its symmetric centralizer has 16 elements,
of which six are even with square one. Signed commutation allows only four
vectors. The independent sign gives the bound 2 · 6 · 4 = 48. The small
certificates below are checked by kernel reduction: a 16-element permutation
table and the 32 even vectors, never subgroups or the whole split extension.

The order-64 subgroup application discharges the nonradical counting premise
of the center calculation for Aschbacher–Smith, combined manuscript
(1 March 2004), I.2.2(6a), printed pp.410 and 412 (PDF pp.421 and 423).
The remaining radical counting premise and source assembly belong to the
parent center development.
-/

public section
open Equiv Subgroup Finset
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions
namespace Nonradical
private abbrev ActorPermutation := Equiv.Perm (Fin 6)
private def doubleTransposition : ActorPermutation := Equiv.swap 0 1 * Equiv.swap 2 3
private def doubleActor : A := ⟨doubleTransposition, by rw [Perm.mem_alternatingGroup]; decide⟩

-- Independent swaps on the three pairs, and interchange of the first two pairs.
private def centralizerElement (i : Fin 16) : ActorPermutation :=
  (if i.val % 2 = 0 then 1 else Equiv.swap 0 1) *
  (if i.val / 2 % 2 = 0 then 1 else Equiv.swap 2 3) *
  (if i.val / 4 % 2 = 0 then 1 else Equiv.swap 4 5) *
  (if i.val / 8 = 0 then 1 else Equiv.swap 0 2 * Equiv.swap 1 3)

private def centralizerElements : Finset ActorPermutation := univ.image centralizerElement

private theorem centralizerElements_card : centralizerElements.card = 16 := by decide +kernel
private theorem centralizerElement_commutes : ∀ i : Fin 16,
    doubleTransposition * centralizerElement i = centralizerElement i * doubleTransposition := by
  decide +kernel

private def actorCandidates : Finset ActorPermutation :=
  centralizerElements.filter (fun p => p.sign = 1 ∧ p * p = 1)
private def vectorCandidates : Finset V := univ.filter (fun w =>
  permuteVector doubleTransposition w = w ∧ signedCorrection doubleTransposition w = 0)
private theorem actorCandidates_card : actorCandidates.card = 6 := by decide +kernel
private theorem vectorCandidates_card : vectorCandidates.card = 4 := by decide +kernel

-- Radical conjugation changes v by u + doubleTransposition(u). The only
-- remaining coordinate is the common value on the last pair, hence volume.
private theorem vector_normalization : ∀ v : V, permuteVector doubleTransposition v = v →
    ∃ u : V, u + v + permuteVector doubleTransposition u = 0 ∨
      u + v + permuteVector doubleTransposition u = volumeVector := by decide +kernel

private theorem centralizer_card :
    Nat.card (centralizer ({doubleTransposition} : Set ActorPermutation)) = 16 := by
  rw [Perm.nat_card_centralizer, show doubleTransposition.cycleType = {2, 2} by decide +kernel]
  norm_num

-- The centralizer order formula proves that the displayed table is exhaustive.
private theorem mem_centralizerElements (p : ActorPermutation)
    (hp : doubleTransposition * p = p * doubleTransposition) : p ∈ centralizerElements := by
  classical
  let C : Subgroup ActorPermutation := centralizer {doubleTransposition}
  have he : centralizerElements = (C : Set ActorPermutation).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      apply Set.mem_toFinset.mpr
      exact mem_centralizer_singleton_iff.mpr (centralizerElement_commutes i).symm
    · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      change Nat.card (centralizer ({doubleTransposition} : Set ActorPermutation)) ≤
        centralizerElements.card
      rw [centralizer_card, centralizerElements_card]
  rw [he]
  exact Set.mem_toFinset.mpr (mem_centralizer_singleton_iff.mpr hp.symm)

private theorem actor_isConj (a : A) (ha : a ^ 2 = 1) (hne : a ≠ 1) : IsConj a doubleActor := by
  apply IsConj.symm
  apply alternatingGroup.isConj_of
  · apply Perm.isConj_iff_cycleType_eq.mpr
    exact (show doubleActor.val.cycleType = {2, 2} by decide +kernel).trans
      (alternatingGroup.involution_cycleType_of_degree_le_six (by decide) a
        (orderOf_eq_prime ha hne)).symm
  · decide +kernel

private theorem conjugate_square_mem (g x : SplitExtension) (hx : x ^ 2 ∈ sign) :
    (MulAut.conj g x) ^ 2 ∈ sign := by
  rw [← map_pow]
  have hc := mem_center_iff.mp (central_le_center (sign_le_central hx)) g
  simpa only [MulAut.conj_apply, hc, mul_inv_cancel_right] using hx

private theorem card_le_conjugate (g x : SplitExtension) :
    Nat.card (squareCommutants x) ≤ Nat.card (squareCommutants (MulAut.conj g x)) := by
  apply Nat.card_le_card_of_injective
    (fun y : squareCommutants x => (⟨MulAut.conj g y.val,
      conjugate_square_mem g y.val y.property.1,
      y.property.2.map (MulAut.conj g)⟩ : squareCommutants (MulAut.conj g x)))
  intro y z h
  exact Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))

private theorem central_of_vector (m : Model) (hm : m.vector = 0 ∨ m.vector = volumeVector) :
    m ∈ center Model := by
  rcases hm with hm | hm
  · exact signKernel_le_center ((mem_signKernel m).mpr hm)
  · have he : m = centralSign m.sign * volume := by
      apply Model.ext
      · simp [centralSign_mul, volume]
      · simpa only [centralSign_mul, volume] using hm
    rw [he]
    exact (center Model).mul_mem (centralSign_mem_center _) Structure.volume_mem_center

private theorem card_le_pure (x : SplitExtension) (hr : x.right = doubleActor)
    (hc : x.left ∈ center Model) :
    Nat.card (squareCommutants x) ≤
      Nat.card (squareCommutants (SemidirectProduct.inr doubleActor)) := by
  have hz : radicalEmbedding x.left ∈ center SplitExtension :=
    central_le_center ⟨x.left, hc, rfl⟩
  have hxy (y : SplitExtension) (h : Commute x y) :
      Commute (SemidirectProduct.inr doubleActor : SplitExtension) y := by
    have he : radicalEmbedding x.left * SemidirectProduct.inr doubleActor = x := by
      rw [← hr]
      exact SemidirectProduct.inl_left_mul_inr_right x
    apply mul_left_cancel (a := radicalEmbedding x.left)
    calc
      radicalEmbedding x.left * (SemidirectProduct.inr doubleActor * y) = x * y := by
        rw [← mul_assoc, he]
      _ = y * x := h.eq
      _ = y * (radicalEmbedding x.left * SemidirectProduct.inr doubleActor) :=
        congrArg (y * ·) he.symm
      _ = radicalEmbedding x.left * (y * SemidirectProduct.inr doubleActor) := by
        rw [← mul_assoc, mem_center_iff.mp hz y, mul_assoc]
  exact Nat.card_le_card_of_injective
    (fun y : squareCommutants x => (⟨y.val, y.property.1, hxy y.val y.property.2⟩ :
      squareCommutants (SemidirectProduct.inr doubleActor)))
    (fun _ _ h => Subtype.ext (congrArg
      (fun t : squareCommutants (SemidirectProduct.inr doubleActor) => t.val) h))

-- Forgetting the actor's additional fixed-vector condition gives an injection
-- into sign × six actors × four vectors, which is sufficient for the bound.
private theorem pure_card_le :
    Nat.card (squareCommutants (SemidirectProduct.inr doubleActor)) ≤ 48 := by
  have ha (y : squareCommutants (SemidirectProduct.inr doubleActor)) :
      y.val.right.val ∈ actorCandidates := by
    obtain ⟨⟨hs, _⟩, hc, _, _⟩ :=
      (mem_squareCommutants_iff_coordinates (SemidirectProduct.inr doubleActor) y.val).mp y.property
    apply Finset.mem_filter.mpr
    refine ⟨mem_centralizerElements _ (congrArg Subtype.val hc),
      Perm.mem_alternatingGroup.mp y.val.right.property, ?_⟩
    exact congrArg Subtype.val (by simpa only [pow_two] using hs)
  have hv (y : squareCommutants (SemidirectProduct.inr doubleActor)) :
      y.val.left.vector ∈ vectorCandidates := by
    obtain ⟨_, _, hv, hc⟩ :=
      (mem_squareCommutants_iff_coordinates (SemidirectProduct.inr doubleActor) y.val).mp y.property
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa [doubleActor] using hv
    · simpa [doubleActor, permuteVector, cocycle] using hc
  let f : squareCommutants (SemidirectProduct.inr doubleActor) →
      F × ↥actorCandidates × ↥vectorCandidates :=
    fun y => (y.val.left.sign, ⟨y.val.right.val, ha y⟩, ⟨y.val.left.vector, hv y⟩)
  have hf : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Model.ext
      · exact congrArg (fun t => t.1) h
      · exact congrArg (fun t => t.2.2.val) h
    · exact Subtype.ext (congrArg (fun t => t.2.1.val) h)
  have hn := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    actorCandidates_card, vectorCandidates_card, ZMod.card, Nat.reduceMul] using hn

private theorem representative_card_le (x : SplitExtension) (hx : x ^ 2 ∈ sign)
    (hr : x.right = doubleActor) : Nat.card (squareCommutants x) ≤ 48 := by
  have hv : permuteVector doubleTransposition x.left.vector = x.left.vector := by
    simpa only [hr, doubleActor] using ((square_mem_sign_iff x).mp hx).2
  obtain ⟨u, hu⟩ := vector_normalization x.left.vector hv
  let g : SplitExtension := radicalEmbedding ⟨0, u⟩
  let z := MulAut.conj g x
  have hzR : z.right = doubleActor := by
    simp [z, g, MulAut.conj_apply, hr]
  have hzV : z.left.vector = u + x.left.vector + permuteVector doubleTransposition u := by
    simp only [z, g, MulAut.conj_apply, SemidirectProduct.mul_left,
      SemidirectProduct.inv_left, SemidirectProduct.right_inl, SemidirectProduct.left_inl,
      SemidirectProduct.mul_right, one_mul, inv_one, map_one, MulAut.one_apply,
      mul_vector, inv_vector, action_apply, signedTo, hr]
    rfl
  have hzc : z.left ∈ center Model := central_of_vector _ (hzV ▸ hu)
  exact (card_le_conjugate g x).trans ((card_le_pure z hzR hzc).trans pure_card_le)
end Nonradical

/-- A square-admissible element with nontrivial actor has fewer than 64
square-admissible commuting elements in the literal signed split extension. -/
theorem squareCommutants_card_lt (x : SplitExtension)
    (hx : x ^ 2 ∈ sign) (hr : x.right ≠ 1) : Nat.card (squareCommutants x) < 64 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (Nonradical.actor_isConj x.right ((square_mem_sign_iff x).mp hx).1 hr)
  let k : SplitExtension := SemidirectProduct.inr g
  have he : (MulAut.conj k x).right = Nonradical.doubleActor := by
    simpa only [k, MulAut.conj_apply, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right, SemidirectProduct.right_inr] using hg
  have hle := (Nonradical.card_le_conjugate k x).trans
    (Nonradical.representative_card_le _ (Nonradical.conjugate_square_mem k x hx) he)
  omega

/-- In an order-64 subgroup with all squares in the sign layer, every central
member lies in the Clifford radical. This uses the published subgroup injection. -/
theorem center_right_eq_one (H : Subgroup SplitExtension) (hcard : Nat.card H = 64)
    (hsq : ∀ y ∈ H, y ^ 2 ∈ sign) (z : H) (hz : z ∈ center H) : z.val.right = 1 := by
  by_contra hn
  have hc (y : SplitExtension) (hy : y ∈ H) : Commute z.val y :=
    (congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)).symm
  have hlo := card_le_squareCommutants H hsq z.val hc
  have hhi := squareCommutants_card_lt z.val (hsq z.val z.property) hn
  omega
end EvenCliffordSix.SplitExtension.ElementaryRestrictions
