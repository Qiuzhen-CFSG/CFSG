module

public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.Geometry
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.CentralAction
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.OddDihedral

/-!
# Two-conjugate core geometry: E.2.10

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp. 222–224.

`TwoConjugate.Hypotheses` records the exact local setup, including relative
normality and the intrinsic local two-core. This module assembles parts
(1)–(6) and (9). The elementary geometry identifies the two-core intersections
with the source's core intersections. Central commutator maps prove centrality
of `J/P`; this discharges the premise of the odd dihedral recognition theorem.
Self-centralization of the intrinsic generalized Fitting subgroup and coprime
action give (9). The quotient summands are actual images in `X/Z`, and the
dihedral conclusions are multiplicative equivalences with `DihedralGroup m`.

Parts (7) and (8), which concern other quotient models, belong to the separate
central-extension development.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- E.2.10(6), with the central-action premise discharged by part (4). -/
theorem odd_dihedral (h : Hypotheses T V M g)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.core_geometry.1
    P V M g = pCore 2 X ∧ pCore 2 X = J M ∧
      ∃ m : ℕ, 0 < m ∧ Odd m ∧
        Nonempty ((X ⧸ P V M g) ≃* DihedralGroup m) ∧
        Nonempty ((X ⧸ J M) ≃* DihedralGroup m) :=
  h.odd_dihedral_of_card_two h.commutator_J_le_P hcard

/-- The core assertions of E.2.10: parts (1), (2), (3), (4), (5), (6), and
(9), in that order. The two conditional clauses retain exactly their source
hypotheses; all preceding structural premises have been discharged. -/
theorem proposition_E_2_10_core (h : Hypotheses T V M g) :
    letI := h.core_geometry.1
    letI := h.Z_normal
    let q := QuotientGroup.mk' (Z V g)
    ((P V M g).Normal ∧
      (P V M g : Set X) = (B V M : Set X) * (A V M g : Set X) ∧
      Z V g ≤ P V M g ⊓ center X) ∧
    (IsElementaryAbelian 2 ((P V M g).map q) ∧
      (B V M).map q ⊔ (A V M g).map q = (P V M g).map q ∧
      (B V M).map q ⊓ (A V M g).map q = ⊥ ∧
      ⁅⁅(P V M g).map q, V.map q⁆, V.map q⁆ = ⊥ ∧
      (P V M g).map q ⊓ centralizer (V.map q : Set (X ⧸ Z V g)) =
        (B V M).map q) ∧
    pCore 2 (X ⧸ J M) = ⊥ ∧
    ⁅J M, (⊤ : Subgroup X)⁆ ≤ P V M g ∧
    ⁅⁅⁅V, A V M g⁆, A V M g⁆, A V M g⁆ = ⊥ ∧
    (Nat.card (V.map (QuotientGroup.mk' (J M))) = 2 →
      P V M g = pCore 2 X ∧ pCore 2 X = J M ∧
        ∃ m : ℕ, 0 < m ∧ Odd m ∧
          Nonempty ((X ⧸ P V M g) ≃* DihedralGroup m) ∧
          Nonempty ((X ⧸ J M) ≃* DihedralGroup m)) ∧
    (V ≠ ⊤ → Theory.GroupTheory.generalizedFitting X = pCore 2 X →
      ⁅V, A V M g⁆ ≠ ⊥) := by
  let := h.core_geometry.1
  let := h.Z_normal
  exact ⟨h.core_geometry,
    ⟨h.quotient_direct_sum.1, h.quotient_direct_sum.2.1,
      h.quotient_direct_sum.2.2, h.quotient_quadratic, h.quotient_fixed_eq_B⟩,
    h.quotient_twoCore_eq_bot, h.commutator_J_le_P, h.cubic,
    h.odd_dihedral, h.commutator_V_A_ne_bot⟩

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
