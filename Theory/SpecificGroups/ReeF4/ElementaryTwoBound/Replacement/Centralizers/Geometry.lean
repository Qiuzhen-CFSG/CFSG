module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.Centralizers.Roots
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.IndexBound

/-!
# The elementary root plane in the Ree replacement

The literal join V = Y₃Y₅ is parametrized injectively by two field elements.
Both curves are additive and C centralizes them. The resulting plane has
order Q², its Y₅ line has order Q, and every element has square one.
Source: GLS3 2.4.5(d), 2.4.6 and the first paragraph of Lemma 3.3.9.
-/

@[expose] public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.Replacement
open Subgroup Parabolics
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates

namespace CentralizerGeometry

private theorem root_zero (m : ℕ) (r : Theory.AlgebraicGroup.F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 :=
  Subtype.ext (Theory.AlgebraicGroup.F4Chevalley.rootCurve_zero r)

@[simp] theorem rootWord_zero (m : ℕ) (i : Fin 8) : rootWord m i 0 = 1 := by
  simp [rootWord, root_zero]

@[simp] theorem centralWord_zero (m : ℕ) (i : Fin 8) : centralWord m i 0 = 1 := by
  simp [centralWord, root_zero]

@[simp] theorem centralElement_zero (m : ℕ) (i : Fin 8) : centralElement m i 0 = 1 :=
  Subtype.ext (centralWord_zero m i)

@[simp] theorem mainElement_zero (m : ℕ) (i : Fin 8) : mainElement m i 0 = 1 :=
  Subtype.ext (rootWord_zero m i)

/-- Additivity of the central curve in an even-indexed B₂ block. -/
theorem centralElement_add (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0)
    (a b : CoefficientField m) :
    centralElement m i (a + b) = centralElement m i a * centralElement m i b := by
  obtain ⟨j, rfl⟩ : ∃ j, positiveRootWordLayout.quartetIndex j = i := by
    rcases positiveRootWordLayout.positive_covers i with ⟨j, hj⟩ | h
    · exact False.elim ((positiveRootWordLayout.pair_odd j) (hj.symm ▸ hi))
    · exact h
  apply Subtype.ext
  change centralWord m _ (a + b) = centralWord m _ a * centralWord m _ b
  have hc := positiveRootWordLayout.quartet_top_commute m (mixedRootCommutation m) j
    b (rootFieldEnd m (longRoot (positiveRootWordLayout.quartetIndex j)) a)
  have root_add (r : Theory.AlgebraicGroup.F4Chevalley.Root) (u v : CoefficientField m) :
      rootGeneratorInGroup m r (u + v) = rootGeneratorInGroup m r u *
        rootGeneratorInGroup m r v :=
    Subtype.ext (Theory.AlgebraicGroup.F4Chevalley.rootCurve_add r u v)
  simp only [centralWord, map_add, root_add]
  exact hc.mul_mul_mul_comm _ _

theorem centralElement_commute (m : ℕ) (a b : CoefficientField m) :
    Commute (centralElement m 2 a) (centralElement m 4 b) := by
  apply toSplitGroup_injective m
  simpa only [map_mul, centralElement_coe] using (ReplacementCentralizerRoots.central_commute m a b).eq

/-- The source section C centralizes the actual root plane. -/
theorem C_centralizes_V (m : ℕ) : C m ≤ centralizer (V m : Set (Model m)) := by
  have hroot (i : Fin 8) (hi : i ≠ 7) :
      X m i ≤ centralizer (V m : Set (Model m)) := by
    have h (j : Fin 8) (hj : j = 2 ∨ j = 4) :
        X m i ≤ centralizer (Y m j : Set (Model m)) := by
      rw [X, Y, centralizer_closure]
      apply (closure_le _).mpr
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      apply toSplitGroup_injective m
      simp only [map_mul, mainElement_coe, centralElement_coe]
      rcases hj with rfl | rfl
      · exact (ReplacementCentralizerRoots.main_central_2 m i hi a b).symm.eq
      · exact (ReplacementCentralizerRoots.main_central_4 m i a b).symm.eq
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (h 2 (Or.inl rfl)))
      (le_centralizer_iff.mp (h 4 (Or.inr rfl)))
  exact sup_le (sup_le (hroot 0 (by decide))
    (sup_le (sup_le (sup_le (sup_le (hroot 1 (by decide)) (hroot 2 (by decide)))
      (hroot 3 (by decide))) (hroot 4 (by decide))) (hroot 5 (by decide))))
    (hroot 6 (by decide))

/-- The two additive root parameters, in positive block order. -/
def planeHom (m : ℕ) : Multiplicative (CoefficientField m × CoefficientField m) →* Model m where
  toFun p := centralElement m 4 p.toAdd.2 * centralElement m 2 p.toAdd.1
  map_one' := by simp
  map_mul' p q := by
    change centralElement m 4 (p.toAdd.2 + q.toAdd.2) *
        centralElement m 2 (p.toAdd.1 + q.toAdd.1) = _
    rw [centralElement_add m 4 (by decide), centralElement_add m 2 (by decide)]
    exact (centralElement_commute m p.toAdd.1 q.toAdd.2).symm.mul_mul_mul_comm _ _

theorem V_eq_range (m : ℕ) : V m = (planeHom m).range := by
  apply le_antisymm
  · apply sup_le
    · apply (closure_le _).mpr
      rintro _ ⟨a, rfl⟩
      exact ⟨Multiplicative.ofAdd (a, 0), by simp [planeHom]⟩
    · apply (closure_le _).mpr
      rintro _ ⟨b, rfl⟩
      exact ⟨Multiplicative.ofAdd (0, b), by simp [planeHom]⟩
  · rintro _ ⟨p, rfl⟩
    exact (V m).mul_mem ((show Z m ≤ V m from le_sup_right) (subset_closure ⟨p.toAdd.2, rfl⟩))
      ((show Y m 2 ≤ V m from le_sup_left) (subset_closure ⟨p.toAdd.1, rfl⟩))

theorem mem_V_iff (m : ℕ) (x : Model m) :
    x ∈ V m ↔ ∃ a b, centralElement m 4 b * centralElement m 2 a = x := by
  rw [V_eq_range]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.toAdd.1, p.toAdd.2, hp⟩
  · rintro ⟨a, b, h⟩
    exact ⟨Multiplicative.ofAdd (a, b), h⟩

private def planeParameters (m : ℕ) (a b : CoefficientField m) : PositiveParameters m :=
  ⟨fun _ => 0, fun _ => 0, ![0, b, 0, a]⟩

private theorem positiveWord_planeParameters (m : ℕ) (a b : CoefficientField m) :
    positiveWord m (planeParameters m a b) = centralWord m 4 b * centralWord m 2 a := by
  simp [positiveWord, planeParameters, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ]

theorem planeHom_injective (m : ℕ) : Function.Injective (planeHom m) := by
  intro p q h
  have he : planeParameters m p.toAdd.1 p.toAdd.2 =
      planeParameters m q.toAdd.1 q.toAdd.2 := by
    apply positiveWord_injective m
    simpa only [positiveWord_planeParameters, planeHom, MonoidHom.coe_mk,
      OneHom.coe_mk, map_mul, centralElement_coe] using congrArg (toSplitGroup m) h
  apply Multiplicative.ofAdd.injective
  apply Prod.ext
  · exact congrArg (fun r : PositiveParameters m => r.central 3) he
  · exact congrArg (fun r : PositiveParameters m => r.central 1) he

/-- The plane has exactly two independent field parameters. -/
theorem card_V (m : ℕ) : Nat.card (V m) = (2 ^ (2 * m + 1)) ^ 2 := by
  rw [V_eq_range]
  have h := Nat.card_congr (Equiv.ofBijective (planeHom m).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (planeHom_injective m),
      (planeHom m).rangeRestrict_surjective⟩)
  simpa only [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, field_card, pow_two] using h.symm

theorem centralElement_four_injective (m : ℕ) : Function.Injective (centralElement m 4) := by
  intro a b h
  exact EvenInvolutionGeometry.longRootElement_injective m h

def lineHom (m : ℕ) : Multiplicative (CoefficientField m) →* Model m where
  toFun a := centralElement m 4 a.toAdd
  map_one' := centralElement_zero m 4
  map_mul' a b := centralElement_add m 4 (by decide) a.toAdd b.toAdd

theorem Z_eq_range (m : ℕ) : Z m = (lineHom m).range := by
  change closure ((lineHom m).range : Set (Model m)) = _
  exact closure_eq _

theorem card_Z (m : ℕ) : Nat.card (Z m) = 2 ^ (2 * m + 1) := by
  rw [Z_eq_range]
  have h := Nat.card_congr (Equiv.ofBijective (lineHom m).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (centralElement_four_injective m),
      (lineHom m).rangeRestrict_surjective⟩)
  simpa only [Nat.card_congr Multiplicative.toAdd, field_card] using h.symm

theorem elementary_V (m : ℕ) : IsElementaryAbelian 2 (V m) := by
  refine { toIsMulCommutative := (le_centralizer_iff_isMulCommutative.mp
      ((V_le_C m).trans (C_centralizes_V m))), exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  have hx : (x : Model m) ∈ (planeHom m).range := by
    rw [← V_eq_range]
    exact x.property
  obtain ⟨p, hp⟩ := hx
  apply Subtype.ext
  change (x : Model m) ^ 2 = 1
  rw [← hp, ← map_pow]
  have hz : p ^ 2 = 1 := by
    rw [pow_two]
    change (p.toAdd + p.toAdd : CoefficientField m × CoefficientField m) = 0
    exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)
  rw [hz, map_one]

end CentralizerGeometry
end ReeF4.ElementaryTwoBound.Replacement
