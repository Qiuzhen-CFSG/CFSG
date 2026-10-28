module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Commutators
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticRankThree.Comparison

/-!
# The original C₂ projective incidence from the source row

The actual second-parabolic action has three suborbits, with subdegrees
1,q(q+1),q³ and degree q³+q²+q+1. The canonical lift exchanges the base
and neighboring point. The (3G) radical-normality premises and exact
(6A)(a) commutation give the actual q-element pointwise-kernel subgroup.
Thus all orbit and fixation premises of the preceding marked incidence
application are discharged here, retaining the same quotient and markings.
The binary specialization gives 15 points, subdegrees 1,6,8, and kernel
order at least two without invoking a printed q>2 theorem.

This is projective incidence, not coordinatization or group recognition.
Deriving radical normality from the original local quotients remains in
this source family; row selection retains its existing producer. The
geometric continuation must construct the field, null polarity and
normal full symplectic subgroup. The existing
marked comparison remains conditional on that last recognition.
Source: Fong–Seitz I (3G), (6A)(a); II (7C), p.193; Higman (1964), §7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.GroupAction.SymplecticRankThree
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
local notation "a" => C2RankThree.rightCosetPoint Q 1 1
local notation "b" => C2RankThree.neighborPoint Q
local notation "A₀" => MulAction.stabilizer (X ⧸ Q.D) a

include e h in
/-- The actual rank-three source geometry from the (6A)(a) row. Orbit
coverage, both subdegrees, the swap and the kernel bound are discharged. -/
theorem marked_projective_incidence_of_row {q : ℕ} (hq : 2 ≤ q)
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = q)
    (hq1 : Nat.card (simpleRoot Q split 1) = q)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    ∃ D : PolarityDesign (C2RankThree.Points Q 1) q,
      (∀ x y, D.incident x y ↔ y = x ∨
        (MulAction.SwappedOrbital.graph a b (C2RankThree.base_ne_neighbor Q)
          (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
          (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)).Adj x y) ∧
      D.block a = insert a (MulAction.orbit A₀ b) ∧
      (∀ x y, x ≠ y → (D.line x y).ncard = q+1) ∧
      (∀ x y p, x ≠ y → (D.line x y ∩ D.block p).Nonempty) ∧
      (∀ x y z, x ≠ y → z ∉ D.line x y →
        ∃! p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p) ∧
      (∀ x y z w, z ≠ w → x ≠ z → y ≠ w →
        (D.line x y ∩ D.line z w).Nonempty → (D.line x z ∩ D.line y w).Nonempty) ∧
      (∃ x y z w, x ≠ y ∧ z ∉ D.line x y ∧
        ¬ ∃ p, x ∈ D.block p ∧ y ∈ D.block p ∧ z ∈ D.block p ∧ w ∈ D.block p) :=
  marked_projective_incidence Q e h split hq b (C2RankThree.oppositePoint Q)
    (C2RankThree.base_ne_neighbor Q) (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
    (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)
    (C2RankThree.opposite_orbit_eq_compl Q hm) hm hq0
    (C2RankThree.neighbor_orbit_card Q split hm hq0 hq1) hq1
    (C2RankThree.kernelRoot_fixes_of_row Q split hm hV hrow)

/-- The explicit binary source numbers are 15 points, subdegrees 1,6,8,
and at least two elements in the kernel on the seven-point closed orbit.
No q>2 recognition theorem is used. -/
theorem binary_source_counts
    (hm : rotationOrder Q = 4)
    (hq0 : Nat.card (simpleRoot Q split 0) = 2)
    (hq1 : Nat.card (simpleRoot Q split 1) = 2)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥) :
    Nat.card (C2RankThree.Points Q 1) = 15 ∧
      Nat.card (MulAction.orbit A₀ b) = 6 ∧
      Nat.card (MulAction.orbit A₀ (C2RankThree.oppositePoint Q)) = 8 ∧
      2 ≤ Nat.card (fixingSubgroup (X ⧸ Q.D) (insert a (MulAction.orbit A₀ b))) := by
  refine ⟨?_,?_,?_,C2RankThree.source_kernel_lower_bound Q split hm hq1 hV hrow⟩
  · simpa using C2RankThree.points_card Q split hm hq0 hq1 1
  · simpa using C2RankThree.neighbor_orbit_card Q split hm hq0 hq1
  · simpa using C2RankThree.opposite_orbit_card Q split hm hq0 hq1

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticRankThree
