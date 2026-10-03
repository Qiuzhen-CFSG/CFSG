module

public import Stellmacher.Recognition.FongWreathedBorelConstruction
public import Stellmacher.Recognition.SuzukiThreeRecognition

/-!
# Fong's wreathed Sylow recognition

Fong's character calculation and Borel construction produce a faithful
doubly transitive action on 28 points.  The point stabilizer has a normal
regular subgroup of order 27 and cyclic quotient of order 8.  This file
connects those concrete witnesses to Suzuki's q = 3 recognition interface.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), pp. 69--76; Suzuki's recognition theorem is
formalized in `SuzukiThreeRecognition`.
-/

namespace Stellmacher.Recognition.FongWreathed

open MulAction

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Fong's standalone recognition theorem for a height-two wreathed Sylow
2-subgroup and a solvable involution centralizer. -/
public theorem nonempty_equiv_psu3
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G)
    (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    Nonempty (G ≃* ABG.PSU3 3 1 (by decide)) := by
  obtain ⟨P, c, ⟨a⟩, _hG⟩ := exists_borelAction S hS x hx
  have hBstab : a.subgroups.B = stabilizer G a.subgroups.baseCoset := by
    apply le_antisymm
    · intro g hg
      rw [mem_stabilizer_iff]
      exact a.subgroups.smul_baseCoset g hg
    · intro g hg
      rw [mem_stabilizer_iff] at hg
      change ((g * 1 : G) : G ⧸ a.subgroups.B) = ((1 : G) : G ⧸ a.subgroups.B) at hg
      have hm : (g * 1)⁻¹ * 1 ∈ a.subgroups.B := QuotientGroup.eq.mp hg
      have hm' : g⁻¹ ∈ a.subgroups.B := by simpa using hm
      simpa using a.subgroups.B.inv_mem hm'
  let Ω := G ⧸ a.subgroups.B
  let base : Ω := a.subgroups.baseCoset
  let : FaithfulSMul G Ω := a.faithful
  let Q : Subgroup (stabilizer G base) :=
    a.subgroups.Q.subgroupOf (stabilizer G base)
  have hQle : a.subgroups.Q ≤ stabilizer G base := by
    intro q hq
    rw [mem_stabilizer_iff]
    exact a.subgroups.smul_baseCoset q (a.subgroups.Q_le_B hq)
  let : Q.Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (hBstab.ge.trans a.subgroups.Q_normalized)
  have hreg : ∀ y z : Ω, y ≠ base → z ≠ base →
      ∃! q : Q, (q : G) • y = z := by
    intro y z hy hz
    obtain ⟨q, hq, hquniq⟩ := a.regular y z hy hz
    let q' : Q := ⟨⟨(q : G), hQle q.property⟩,
      (Subgroup.mem_subgroupOf).2 q.property⟩
    refine ⟨q', ?_, ?_⟩
    · simpa [q'] using hq
    · intro r hr
      apply Subtype.ext
      let r' : a.subgroups.Q :=
        ⟨(r : G), (Subgroup.mem_subgroupOf).mp r.property⟩
      have he := hquniq r' (by simpa [r'] using hr)
      apply Subtype.ext
      change (r : G) = (q : G)
      exact congrArg Subtype.val he
  let h : SuzukiThreeHypotheses G Ω base Q := {
    degree := by simpa [Ω, base] using a.degree,
    doubly_transitive := a.doubly_transitive,
    regular := hreg,
    quotient_cyclic := by
      let e := QuotientGroup.equivQuotientSubgroupOfOfEq
        (A' := a.subgroups.Q) (A := stabilizer G base)
        (B' := a.subgroups.Q) (B := a.subgroups.B) rfl hBstab.symm
      exact e.isCyclic.mpr a.subgroups.quotient_cyclic,
    quotient_card := by
      let e := QuotientGroup.equivQuotientSubgroupOfOfEq
        (A' := a.subgroups.Q) (A := stabilizer G base)
        (B' := a.subgroups.Q) (B := a.subgroups.B) rfl hBstab.symm
      exact (Nat.card_congr e.toEquiv).trans a.subgroups.card_quotient
  }
  exact h.nonempty_equiv_psu3Three

end Stellmacher.Recognition.FongWreathed
