module

public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section10.Reducible.PairAction
public import CFSG.Quasithin.ChapterG.Section10.FittingSource
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The plane and reducible branches of G.11.2

The plane action is the full binary linear group, hence S₃. In the reducible
case the existing G.10 argument embeds the group into S₃ × S₃. Its marked
point has an odd orbit spanning a four-space. The orbit index divides 36
and is at least four, so it equals nine. The low-rank witness supplies an
involution; hence the group order is divisible by eighteen.

The same order clause is proved for every solvable four-dimensional action:
the irreducible cubic branch has a three-core of order nine, and the other
branch has a dihedral normal closure of order ten. These statements discharge
the small branches in the low-rank G.11.2 assembly. They do not assert an
exhaustive classification in higher dimensions.

Source: Aschbacher--Smith G.10.5, G.11.2(1--2), and G.11.4--5,
printed pp.359,364--365.
-/

@[expose] public section
open Subgroup Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- G.11.2(1). The theorem below additionally identifies every linear operator. -/
def CaseOne (_ρ : Representation (ZMod 2) G V) : Prop :=
  finrank (ZMod 2) V = 2 ∧ Nonempty (G ≃* Equiv.Perm (Fin 3))

/-- G.11.2(2). Faithfulness and preservation express the original action as a
subgroup of the isometry group of the given form. The order clause is essential. -/
def CaseTwo (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V) : Prop :=
  finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card G ∨ 18 ∣ Nat.card G) ∧
    Function.Injective ρ ∧ B.IsAlt ∧ B.Nondegenerate ∧
    ∀ g x y, B (ρ g x) (ρ g y) = B x y

variable {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Section10.Hypothesis ρ B v W X X₀)
include h

/-- The orbit-generation clause bounds the dimension by the literal point
centralizer index. This uses the original vector, not a substitute marker. -/
theorem degree_le_pointCentralizer_index :
    finrank (ZMod 2) V ≤ (Section10.pointCentralizer ρ v).index := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulAction G V := {
    smul := fun g w => ρ g w
    one_smul := by intro w; change ρ 1 w = w; simp
    mul_smul := by intro g k w; change ρ (g * k) w = ρ g (ρ k w); simp }
  let O := MulAction.orbit G v
  let : Fintype O := Fintype.ofFinite O
  have hO : O = {w | ∃ g : G, ρ g v = w} := rfl
  have hc : (MulAction.stabilizer G v) = Section10.pointCentralizer ρ v := rfl
  have hb := finrank_span_le_card (R := ZMod 2) O
  have hspan : Submodule.span (ZMod 2) O = ⊤ := by
    rw [hO]
    exact h.orbit_span
  rw [hspan, finrank_top] at hb
  have hi : (Section10.pointCentralizer ρ v).index = O.toFinset.card := by
    rw [← hc, MulAction.index_stabilizer]
    exact (Nat.card_eq_fintype_card).trans (Set.toFinset_card O).symm
  exact hi ▸ hb

/-- Reducibility forces the source order-divisibility clause, in addition to
the dimension already supplied by G.10.4. -/
theorem reducible_order (hw : LowRankWitness ρ v X) (hred : ¬ IsIrreducible ρ) :
    finrank (ZMod 2) V = 4 ∧ 18 ∣ Nat.card G := by
  obtain ⟨f, hf⟩ := h.reducible_symmetricThree_pair hred
  have hcard : Nat.card G ∣ 36 := by
    have hd := Subgroup.card_dvd_of_injective f hf
    simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Nat.factorial] using hd
  have hi36 := (Section10.pointCentralizer ρ v).index_dvd_card.trans hcard
  have hi4 : 4 ≤ (Section10.pointCentralizer ρ v).index := by
    simpa only [(h.reducible_degree_and_solvable hred).1] using degree_le_pointCentralizer_index h
  have hi9 : (Section10.pointCentralizer ρ v).index = 9 := by
    have hm := Nat.mem_divisors.mpr ⟨hi36, by decide⟩
    rw [show Nat.divisors 36 = {1,2,3,4,6,9,12,18,36} by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    obtain ⟨k, hk⟩ := h.odd_index
    rcases hm with hh | hh | hh | hh | hh | hh | hh | hh | hh <;>
      omega
  have h9 : 9 ∣ Nat.card G := hi9 ▸ (Section10.pointCentralizer ρ v).index_dvd_card
  obtain ⟨a, _, ha, _⟩ := hw.exists_involution h.point_ne_zero
  have h2 : 2 ∣ Nat.card G := ha ▸ orderOf_dvd_natCard a
  exact ⟨(h.reducible_degree_and_solvable hred).1,
    (show Nat.Coprime 2 9 by decide).mul_dvd_of_dvd_of_dvd h2 h9⟩

/-- The complete reducible branch of G.11.2(2), including its order condition. -/
theorem caseTwo_of_reducible (hw : LowRankWitness ρ v X) (hred : ¬ IsIrreducible ρ) :
    CaseTwo ρ B := by
  obtain ⟨hd, ho⟩ := reducible_order h hw hred
  exact ⟨hd, Or.inr ho, h.faithful, h.alternating, h.nondegenerate, h.preserves⟩

/-- In dimension two the original representation is the full linear action. -/
theorem plane_full_action (hw : LowRankWitness ρ v X) (hd : finrank (ZMod 2) V = 2) :
    ∃ e : G ≃* (V ≃ₗ[ZMod 2] V), ∀ g w, e g w = ρ g w := by
  have hi : IsIrreducible ρ := by
    by_contra hn
    have hh := (h.reducible_degree_and_solvable hn).1
    omega
  let : IsIrreducible ρ := hi
  exact Section09.FittingRecognition.plane_full_linear_action (setup h)
    (hw.actor_rank_pos h.point_ne_zero) hd

/-- G.11.2(1), with no SQTK classification assumption needed in this degree. -/
theorem caseOne_of_degree_two (hw : LowRankWitness ρ v X) (hd : finrank (ZMod 2) V = 2) :
    CaseOne ρ := by
  obtain ⟨e, _⟩ := plane_full_action h hw hd
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hd
  let t := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm
  let s := (BinaryLinear.OuterCyclic.matrixEquivLinear 2).trans
    ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
  exact ⟨hd, ⟨e.trans (t.trans s)⟩⟩

/-- All solvable four-dimensional source actions satisfy alternative (2).
The cubic branch contributes eighteen, the noncubic branch ten. -/
theorem caseTwo_of_solvable_degree_four {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G)) (hw : LowRankWitness ρ v X)
    (hs : Group.IsSolvable G) (hd : finrank (ZMod 2) V = 4) : CaseTwo ρ B := by
  by_cases hi : IsIrreducible ρ
  · have d := h.fittingHypothesis_of_solvable cover hs hi
    have hm := hw.actor_rank_pos h.point_ne_zero
    refine ⟨hd, ?_, h.faithful, h.alternating, h.nondegenerate, h.preserves⟩
    by_cases hc : IsPGroup 3 (⁅fittingSubgroup G, X⁆ : Subgroup G)
    · have h9c := Section09.FittingRecognition.Four.threeCore_card_nine_of_solvable d hm hc hd hs
      have h9 : 9 ∣ Nat.card G := h9c ▸ (pCore 3 G).card_subgroup_dvd_card
      obtain ⟨a, _, ha, _⟩ := hw.exists_involution h.point_ne_zero
      have h2 : 2 ∣ Nat.card G := ha ▸ orderOf_dvd_natCard a
      exact Or.inr ((show Nat.Coprime 2 9 by decide).mul_dvd_of_dvd_of_dvd h2 h9)
    · obtain ⟨e⟩ := (Section09.FittingRecognition.caseTwo_from_source d hm hc).2.2
      have he : Nat.card (normalClosure (X : Set G)) = 10 := by
        rw [Nat.card_congr e.toEquiv]
        exact DihedralGroup.nat_card (n := 5)
      exact Or.inl (he ▸ (normalClosure (X : Set G)).card_subgroup_dvd_card)
  · exact caseTwo_of_reducible h hw hi

end CFSG.Quasithin.ChapterG.Section11
