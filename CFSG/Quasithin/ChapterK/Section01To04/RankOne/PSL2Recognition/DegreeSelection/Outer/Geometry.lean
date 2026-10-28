module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Inner
public import Theory.SpecificGroups.PSL2.BinaryOuterGeometry

/-!
# Outer PSL₂ geometry on the original Chapter K group

The actual layer marking and its trivial ambient centralizer transport the
half-degree outer-actor bound to G. The fixed-group descent retains the
literal subgroup L ∩ C_G(t), whose two-core is trivial even in the smallest
case. These are the group inputs for the two Schur-field branches of the
degree argument; they impose no degree or module-recognition hypothesis.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.1,
manuscript p.22; Aschbacher--Smith, K.3.1, printed pp.451,453--454.
-/

public section
open scoped MatrixGroups IsMulCommutative
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

private noncomputable def binaryMarking {r : ℕ} (hr : 0 < r)
    (hc : Nat.card K = 2 ^ r) : L ≃* Theory.PSL2.BinaryGroup r := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype (Theory.PSL2.BinaryField r) := Fintype.ofFinite _
  let eF : K ≃+* Theory.PSL2.BinaryField r := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hc,
      GaloisField.card 2 r hr.ne'])
  exact e.trans ((Atlas.fieldEquivSL 2 eF).trans
    (Theory.PSL2.sl2QuotientEquiv (Theory.PSL2.BinaryField r)))

include h e

omit [FiniteDimensional (ZMod 2) V] in
/-- The actual outer actor has at most one generator beyond its half-degree
inner kernel; rank greater than one forces a nontrivial inner intersection. -/
theorem psl2_outer_actor_rank {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r) {A : Subgroup G} (hA : IsElementaryTwo A)
    (hAL : ¬ A ≤ L) :
    2 * rank A ≤ r + 2 ∧ (1 < rank A → A ⊓ L ≠ ⊥) := by
  let : L.Normal := h.layer_normal
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨m, _, hrm, hcard, hbot⟩ :=
    Theory.PSL2.BinaryOuterGeometry.outer_elementary_card_bound L
      (binaryMarking e (by omega) hc) (h.psl2_centralizer_eq_bot e) hr A hAL
  rw [hA.card_eq_two_pow_rank] at hcard hbot
  have hR : rank A ≤ m + 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  refine ⟨by omega, ?_⟩
  intro hlarge he
  have hh : 2 ^ rank A ≤ 2 ^ 1 := hbot he
  have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- The literal layer centralizer has trivial two-core, including PSL₂(2). -/
theorem psl2_outer_centralizer_twoCore_eq_bot {r : ℕ} (hr : 2 ≤ r)
    (hc : Nat.card K = 2 ^ r) (t : G) (ht : t ^ 2 = 1) (htL : t ∉ L) :
    pCore 2 ↥(L ⊓ centralizer {t}) = ⊥ := by
  let : L.Normal := h.layer_normal
  exact Theory.PSL2.BinaryOuterGeometry.outer_fixed_twoCore_eq_bot L
    (binaryMarking e (by omega) hc) (h.psl2_centralizer_eq_bot e) hr t ht htL

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
