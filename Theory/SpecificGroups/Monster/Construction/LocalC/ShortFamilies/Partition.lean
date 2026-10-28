module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.PureFour
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Octads
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Odd

/-!
# Partition and identification of the short extraspecial families

The three minimal Leech shapes give a partition of the actual short elements
of `Q1Image`, using the fixed source lattice comparison. Parity separates the
odd family from the two even families, and the magnitude supports separate
the two even families. These invariants survive negation, so they descend
through reduction modulo twice the lattice.

The octad, odd and pure-four exhaustions then give all four source words,
including both central signs. For the pure-four words equality recovers the
unordered point pair, and their chosen group lifts never equal an opposite
central lift. The octad and odd parameter identifications, explicit Leech
representatives, tensors and corrections are re-exported from their modules.

Source: Michael Aschbacher, *Sporadic Groups*, Lemma 27.8(1)–(4), printed
p. 150 (PDF page 81, left page).
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators DirectSum
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

theorem hasShape_congr {q r : Lift}
    (h : shortLiftClass sourceLatticeComparison q = shortLiftClass sourceLatticeComparison r)
    (S : Finset IntegerCoordinates) : HasShape S q ↔ HasShape S r := by
  simp only [HasShape, h]

theorem twoFour_classes_ne {k n l m : ℕ} (h : k ≠ l ∨ n ≠ m) {q r : Lift}
    (hq : HasShape (twoFourFamily k n) q) (hr : HasShape (twoFourFamily l m) r) :
    shortLiftClass sourceLatticeComparison q ≠ shortLiftClass sourceLatticeComparison r := by
  intro he
  obtain ⟨a, ha, hsa⟩ := hq
  obtain ⟨b, hb, hsb⟩ := hr
  have hab := ha.trans (he.trans hb.symm)
  have hpa := twoFourFamily_shape k n _ hsa
  have hpb := twoFourFamily_shape l m _ hsb
  rcases h with h | h
  · exact h (hpa.2.1.symm.trans ((congrArg Finset.card
      (support_eq_of_reduction_eq a b hab 2)).trans hpb.2.1))
  · exact h (hpa.2.2.symm.trans ((congrArg Finset.card
      (support_eq_of_reduction_eq a b hab 4)).trans hpb.2.2))

theorem even_odd_classes_ne {k n : ℕ} {q r : Lift}
    (hq : HasShape (twoFourFamily k n) q) (hr : HasShape (oddNoFiveVectors 1) r) :
    shortLiftClass sourceLatticeComparison q ≠ shortLiftClass sourceLatticeComparison r := by
  intro he
  obtain ⟨a, ha, hsa⟩ := hq
  obtain ⟨b, hb, hsb⟩ := hr
  have hab := ha.trans (he.trans hb.symm)
  let i : Omega := ((0,0),0)
  have ha0 : a.val.val i % 2 = 0 := by
    rcases (twoFourFamily_shape k n _ hsa).1 i with h | h | h | h | h <;> omega
  have hb1 := ((odd_minimal_shell_iff _).mpr hsb).2.1 i
  rcases (shortReduction_eq_iff a b).mp hab with h | h
  · have hh := congrArg (fun v : leech => v.val i) h
    omega
  · have hh := congrArg (fun v : leech => v.val i) h
    change a.val.val i = -b.val.val i at hh
    omega

/-- The three coordinate shapes in 27.8(1). -/
inductive ShellKind
  | octad | odd | pureFour
  deriving DecidableEq

def shellFamily : ShellKind → Finset IntegerCoordinates
  | .octad => twoFourFamily 8 0
  | .odd => oddNoFiveVectors 1
  | .pureFour => twoFourFamily 0 2

theorem different_shapes_classes_ne {i j : ShellKind} (hij : i ≠ j) {q r : Lift}
    (hq : HasShape (shellFamily i) q) (hr : HasShape (shellFamily j) r) :
    shortLiftClass sourceLatticeComparison q ≠ shortLiftClass sourceLatticeComparison r := by
  cases i <;> cases j
  all_goals try exact (hij rfl).elim
  · exact even_odd_classes_ne hq hr
  · exact twoFour_classes_ne (Or.inl (by decide)) hq hr
  · exact (even_odd_classes_ne hr hq).symm
  · exact (even_odd_classes_ne hr hq).symm
  · exact twoFour_classes_ne (Or.inl (by decide)) hq hr
  · exact even_odd_classes_ne hq hr

/-- Every actual short element lies in exactly one of the three source families. -/
theorem shape_partition (q : Lift) : ∃! i : ShellKind, HasShape (shellFamily i) q := by
  have hex : ∃ i : ShellKind, HasShape (shellFamily i) q := by
    rcases shape_trichotomy q with h | h | h
    · exact ⟨.octad, h⟩
    · exact ⟨.odd, h⟩
    · exact ⟨.pureFour, h⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra h
  exact different_shapes_classes_ne h hj hi rfl

/-- The explicit source words exhaust the actual extraspecial short elements. -/
theorem families_exhaustion (q : Lift) :
    (∃ p : OctadParameters, rOctad p = q) ∨
    (∃ x : Omega, ∃ d : ParkerLoop, rOdd x d = q) ∨
    (∃ x y : Omega, ∃ hxy : x ≠ y,
      q = ru x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (ru x y hxy) ∨
      q = rv x y hxy ∨ q = (shortLiftSigns sourceLatticeComparison).flip (rv x y hxy)) := by
  rcases shape_trichotomy q with h | h | h
  · exact Or.inl ((octad_hasShape_iff q).mp h)
  · exact Or.inr (Or.inl ((odd_iff q).mp h))
  · exact Or.inr (Or.inr ((pureFour_iff q).mp h))

theorem ru_eq_iff (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    ru x y hxy = ru z t hzt ↔ ({x,y} : Finset Omega) = {z,t} :=
  ⟨fun h => (ru_class_eq_iff x y z t hxy hzt).mp
    (congrArg (shortLiftClass sourceLatticeComparison) h),
    ru_eq_of_pair_eq x y z t hxy hzt⟩

theorem rv_eq_iff (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    rv x y hxy = rv z t hzt ↔ ({x,y} : Finset Omega) = {z,t} :=
  ⟨fun h => (rv_class_eq_iff x y z t hxy hzt).mp
    (congrArg (shortLiftClass sourceLatticeComparison) h),
    rv_eq_of_pair_eq x y z t hxy hzt⟩

theorem ru_ne_flip (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    ru x y hxy ≠ (shortLiftSigns sourceLatticeComparison).flip (ru z t hzt) := by
  intro h
  have hc := (shortLiftClass_eq_iff sourceLatticeComparison _ _).mpr (Or.inr h)
  have hp := (ru_class_eq_iff x y z t hxy hzt).mp hc
  rw [ru_eq_of_pair_eq x y z t hxy hzt hp] at h
  exact (shortLiftSigns sourceLatticeComparison).fixedPointFree _ h.symm

theorem rv_ne_flip (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    rv x y hxy ≠ (shortLiftSigns sourceLatticeComparison).flip (rv z t hzt) := by
  intro h
  have hc := (shortLiftClass_eq_iff sourceLatticeComparison _ _).mpr (Or.inr h)
  have hp := (rv_class_eq_iff x y z t hxy hzt).mp hc
  rw [rv_eq_of_pair_eq x y z t hxy hzt hp] at h
  exact (shortLiftSigns sourceLatticeComparison).fixedPointFree _ h.symm

theorem ru_ne_rv_and_flip (x y z t : Omega) (hxy : x ≠ y) (hzt : z ≠ t) :
    ru x y hxy ≠ rv z t hzt ∧
    ru x y hxy ≠ (shortLiftSigns sourceLatticeComparison).flip (rv z t hzt) :=
  not_or.mp (mt (shortLiftClass_eq_iff sourceLatticeComparison _ _).mpr
    (ru_rv_classes_ne_all x y z t hxy hzt))

theorem form_different_shapes {i j : ShellKind} (hij : i ≠ j) {q r : Lift}
    (hq : HasShape (shellFamily i) q) (hr : HasShape (shellFamily j) r) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison q)
      (shortVector sourceLatticeComparison r) = 0 :=
  form_vector_eq_zero q r (different_shapes_classes_ne hij hq hr)

end Sporadic.Monster.Construction.LocalC.ShortFamilies
