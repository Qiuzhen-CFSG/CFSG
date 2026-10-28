module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.Counting

/-!
# The marked generators and the central lifting twist

The field and diagonal elements belong to the centralizer of the selected
graph-field product. The diagonal has order three, the field has order two,
and the field inverts the diagonal. If the diagonal moves the covering center,
their induced actions have orders three and two and fill its automorphism group.
Thus only nontriviality of the diagonal action remains a center-action model fact.

An intrinsic lift equation w(y) = z*y in L, with z in Z(L), gives a projective
centralizer lift with literal defect z inverse. The witness is the original y;
neither the chosen w nor its lift is replaced.

These are conditional reductions. Constructing the diagonal action and a
nonidentity central twist from the cover is still required for the general
marked-cover theorem. Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137,
manuscript of 1 March 2004.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]

/-- The marked field involution in the chosen graph-field centralizer. -/
@[expose] def fieldInCentralizer {d : Overgroup L} (n : NormalizerGeometry d) :
    centralizerIn n.graphFieldI :=
  ⟨n.fieldI, mem_centralizer_singleton_iff.mpr (by
    change n.fieldI * (n.tauI * n.fieldI) = (n.tauI * n.fieldI) * n.fieldI
    rw [← mul_assoc, n.tau_commutes_field.eq.symm, mul_assoc])⟩

/-- Its square is computed in the actual centralizer. -/
theorem fieldInCentralizer_sq {d : Overgroup L} (n : NormalizerGeometry d) :
    fieldInCentralizer n ^ 2 = 1 := by
  exact Subtype.ext n.field_sq

/-- The original field lift inverts the original diagonal element. -/
theorem fieldInCentralizer_inverts_diagonal {d : Overgroup L}
    (n : NormalizerGeometry d) :
    fieldInCentralizer n * n.diagonalInCentralizer * (fieldInCentralizer n)⁻¹ =
      n.diagonalInCentralizer⁻¹ := by
  exact Subtype.ext (n.field_inverts_three _ n.diagonalElement_mem_three)

/-- Trivial action is pointwise centralization of the actual covering center. -/
theorem centralFourAction_eq_one_iff (d : Overgroup L) (w : I)
    (hw : w ∈ centralizer ((center L).map L.subtype : Set I))
    (x : centralizerIn w) :
    centralFourAction d w x = 1 ↔
      (x : I) ∈ centralizer ((center L).map L.subtype : Set I) := by
  change x ∈ (centralFourAction d w).ker ↔ _
  rw [centralFourAction_ker, centerCentralizer_eq_comap w hw]
  rfl

private theorem full_action_of_inverted_three
    {A H : Type*} [Group A] [IsKleinFour A] [Group H]
    (a : H →* MulAut A) (f d : H)
    (hf : f ^ 2 = 1) (hd : d ^ 3 = 1)
    (hinv : f * d * f⁻¹ = d⁻¹) (hne : a d ≠ 1) :
    Function.Surjective a := by
  classical
  have : Finite A := Nat.finite_of_card_ne_zero (by
    rw [IsKleinFour.card_four]; decide)
  let := Fintype.ofFinite A
  have hd3 : a d ^ 3 = 1 := by rw [← map_pow, hd, map_one]
  have hf2 : a f ^ 2 = 1 := by rw [← map_pow, hf, map_one]
  have hfne : a f ≠ 1 := by
    intro hf1
    have he : a d = (a d)⁻¹ := by
      simpa only [map_mul, map_inv, hf1, inv_one, one_mul, mul_one] using
        congrArg a hinv
    have hd2 : a d ^ 2 = 1 := by
      calc
        _ = (a d)⁻¹ * a d := by rw [pow_two]; exact congrArg (· * a d) he
        _ = 1 := inv_mul_cancel _
    apply hne
    simpa only [pow_succ, hd2, one_mul] using hd3
  have hdorder : orderOf (a d) = 3 := orderOf_eq_prime_iff.mpr ⟨hd3, hne⟩
  have hforder : orderOf (a f) = 2 := orderOf_eq_prime_iff.mpr ⟨hf2, hfne⟩
  have hthree : 3 ∣ Nat.card a.range := by
    rw [← hdorder]
    exact a.range.orderOf_dvd_natCard ⟨d, rfl⟩
  have htwo : 2 ∣ Nat.card a.range := by
    rw [← hforder]
    exact a.range.orderOf_dvd_natCard ⟨f, rfl⟩
  have hlower : 6 ∣ Nat.card a.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) htwo hthree
  have hupper : Nat.card a.range ∣ 6 := by
    rw [← IsKleinFour.card_mulAut A]
    exact a.range.card_subgroup_dvd_card
  apply a.range_eq_top.mp
  apply a.range.eq_top_of_card_eq
  rw [IsKleinFour.card_mulAut]
  exact Nat.dvd_antisymm hupper hlower

/-- A nontrivial diagonal action already forces the full center action. -/
theorem centralFourAction_surjective_of_diagonal_moves (d : Overgroup L)
    (n : NormalizerGeometry d)
    (hd : n.diagonalElement ∉ centralizer ((center L).map L.subtype : Set I)) :
    Function.Surjective (centralFourAction d n.graphFieldI) := by
  let := centralFour_isKleinFour d n.graphFieldI n.graphField_mem_centerCentralizer
  apply full_action_of_inverted_three (centralFourAction d n.graphFieldI)
    (fieldInCentralizer n) n.diagonalInCentralizer (fieldInCentralizer_sq n)
    (Subtype.ext n.diagonalElement_cube) (fieldInCentralizer_inverts_diagonal n)
  exact fun he => hd ((centralFourAction_eq_one_iff d n.graphFieldI
    n.graphField_mem_centerCentralizer n.diagonalInCentralizer).mp he)

/-- An intrinsic central twist gives the literal defect of the same lifted element. -/
theorem liftDefect_of_cover_twist (d : Overgroup L) (w : I)
    (y : L) (z : center L) (htwist : (MulAut.conjNormal w : MulAut L) y = z * y) :
    ∃ x : projectiveCentralizerPreimage d w, (x : I) = y ∧
      (centralizerLiftDefect d w x : I) = (((z : L) : I))⁻¹ := by
  have hI : w * (y : I) * w⁻¹ = ((z : L) : I) * (y : I) :=
    congrArg Subtype.val htwist
  have hcomm : (y : I) * w * (y : I)⁻¹ * w⁻¹ = (((z : L) : I))⁻¹ := by
    calc
      _ = (w * (y : I) * w⁻¹ * (y : I)⁻¹)⁻¹ := by group
      _ = (((z : L) : I) * (y : I) * (y : I)⁻¹)⁻¹ := by rw [hI]
      _ = _ := by rw [mul_inv_cancel_right]
  have hz : projectiveAction L d.cover ((z : L) : I) = 1 := by
    change ((z : L) : I) ∈ (projectiveAction L d.cover).ker
    rw [d.projectiveAction_ker]
    exact mem_map_of_mem _ z.property
  have hy : (y : I) ∈ projectiveCentralizerPreimage d w := by
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (projectiveAction L d.cover) hcomm
    simpa only [map_mul, map_inv, hz, inv_one, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, one_mul] using h
  exact ⟨⟨y, hy⟩, rfl, (centralizerLiftDefect_val d w _).trans hcomm⟩

/-- A nonidentity intrinsic twist supplies the defect required by the counting argument. -/
theorem nontrivial_defect_of_cover_twist (d : Overgroup L) (w : I)
    (y : L) (z : center L) (hz : z ≠ 1)
    (htwist : (MulAut.conjNormal w : MulAut L) y = z * y) :
    ∃ x : projectiveCentralizerPreimage d w, centralizerLiftDefect d w x ≠ 1 := by
  obtain ⟨x, _, hx⟩ := liftDefect_of_cover_twist d w y z htwist
  refine ⟨x, fun he => hz ?_⟩
  have h : (((z : L) : I))⁻¹ = 1 := hx.symm.trans (congrArg Subtype.val he)
  exact Subtype.ext (Subtype.ext (inv_eq_one.mp h))

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers
