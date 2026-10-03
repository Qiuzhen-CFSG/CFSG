module

public import Mathlib.GroupTheory.Frattini
public import Theory.GroupAction.Quotient

/-!
# The quotient actions in Parrott's order-512 argument

Let an order-five group act by automorphisms on a finite two-group `V` of
nilpotency class at least three, and assume that every fixed point in `V` is
central. The action on the Frattini quotient is nontrivial. The action on the
derived subgroup modulo its intersection with the center has trivial fixed
subgroup, and this quotient is nontrivial.

Coprime fixed-point lifting identifies the fixed subgroup of each quotient
with the image of the fixed subgroup upstairs. If the Frattini quotient
were fixed pointwise, Frattini nongeneration would make all of `V` fixed,
hence central. For the derived quotient, all lifted fixed points are
central and therefore vanish. Finally, a trivial derived quotient would
place the derived subgroup inside the center, forcing nilpotency class at
most two. The statement retains the exact induced action on each quotient.

These are the action-theoretic steps behind the two lower bounds at the
start of Lemma 1 in David Parrott, *A characterization of the Tits' simple
group*, Canadian Journal of Mathematics 24 (1972), p. 672. The order of `V`
is not needed until the subsequent cardinality comparison.
-/

open scoped IsMulCommutative

namespace Theory.GroupAction

/-- The two induced quotient actions used in Parrott's order-512 argument. -/
public theorem parrott_quotient_actions
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hclass : 3 ≤ Group.nilpotencyClass V)
    (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ Subgroup.center V) :
    letI : IsInvariant A V (commutator V) :=
      isInvariant_of_characteristic (commutator V)
    letI : IsInvariant A V (Subgroup.center V) :=
      isInvariant_of_characteristic (Subgroup.center V)
    letI : MulDistribMulAction A (V ⧸ frattini V) :=
      quotientMulDistribMulAction (frattini V)
        (isInvariant_of_characteristic (frattini V))
    letI : MulDistribMulAction A
        ((commutator V) ⧸ (Subgroup.center V).subgroupOf (commutator V)) :=
      quotientMulDistribMulAction ((Subgroup.center V).subgroupOf (commutator V))
        (isInvariant_subgroupOf (Subgroup.center V) (commutator V))
    ¬ ActsTrivially A (V ⧸ frattini V) ∧
      FixedPoints.subgroup A
        ((commutator V) ⧸ (Subgroup.center V).subgroupOf (commutator V)) = ⊥ ∧
      Nontrivial ((commutator V) ⧸ (Subgroup.center V).subgroupOf (commutator V)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent V := hV.isNilpotent
  let : IsInvariant A V (commutator V) :=
    isInvariant_of_characteristic (commutator V)
  let : IsInvariant A V (Subgroup.center V) :=
    isInvariant_of_characteristic (Subgroup.center V)
  let : MulDistribMulAction A (V ⧸ frattini V) :=
    quotientMulDistribMulAction (frattini V)
      (isInvariant_of_characteristic (frattini V))
  let : MulDistribMulAction A
      ((commutator V) ⧸ (Subgroup.center V).subgroupOf (commutator V)) :=
    quotientMulDistribMulAction ((Subgroup.center V).subgroupOf (commutator V))
      (isInvariant_subgroupOf (Subgroup.center V) (commutator V))
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    obtain ⟨n, hn⟩ := hV.exists_card_eq
    rw [hA, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  refine ⟨?_, ?_, ?_⟩
  · intro htriv
    have hfixquot : FixedPoints.subgroup A (V ⧸ frattini V) = ⊤ := by
      apply top_unique
      intro q _
      exact (FixedPoints.mem_subgroup _ _ _).mpr (fun a => htriv a q)
    have hmap : (FixedPoints.subgroup A V).map (QuotientGroup.mk' (frattini V)) = ⊤ := by
      rw [← fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
        (inferInstance : Group.IsSolvable V) hcop (frattini V)
        (isInvariant_of_characteristic (frattini V))]
      exact hfixquot
    have hsup : FixedPoints.subgroup A V ⊔ frattini V = ⊤ := by
      simpa [sup_comm] using congrArg (Subgroup.comap (QuotientGroup.mk' (frattini V))) hmap
    have hfixtop : FixedPoints.subgroup A V = ⊤ := frattini_nongenerating hsup
    have hcenter : Subgroup.center V = ⊤ := by
      apply top_unique
      rw [← hfixtop]
      exact hfixed
    have hclass1 : Group.nilpotencyClass V ≤ 1 :=
      Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr
        (Subgroup.center_eq_top_iff.mp hcenter)
    omega
  · rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable (commutator V))
      (hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card (commutator V)))
      ((Subgroup.center V).subgroupOf (commutator V))
      (isInvariant_subgroupOf (Subgroup.center V) (commutator V))]
    apply eq_bot_iff.mpr
    rintro q ⟨d, hd, rfl⟩
    apply (Subgroup.mem_bot).mpr
    apply (QuotientGroup.eq_one_iff (N := (Subgroup.center V).subgroupOf (commutator V)) d).mpr
    apply hfixed
    exact (FixedPoints.mem_subgroup _ _ _).mpr (fun a =>
      congrArg Subtype.val ((FixedPoints.mem_subgroup _ _ _).mp hd a))
  · by_contra hnontriv
    let : Subsingleton
        ((commutator V) ⧸ (Subgroup.center V).subgroupOf (commutator V)) :=
      not_nontrivial_iff_subsingleton.mp hnontriv
    have hcomm : commutator V ≤ Subgroup.center V := by
      intro d hd
      exact (QuotientGroup.eq_one_iff
        (N := (Subgroup.center V).subgroupOf (commutator V)) ⟨d, hd⟩).mp
        (Subsingleton.elim
          (QuotientGroup.mk' ((Subgroup.center V).subgroupOf (commutator V)) ⟨d, hd⟩) 1)
    have hclass2 : Group.nilpotencyClass V ≤ 2 := by
      apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
      exact Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup V)
        (by simpa only [Subgroup.top_lowerCentralSeries_one] using hcomm)
    omega

end Theory.GroupAction
