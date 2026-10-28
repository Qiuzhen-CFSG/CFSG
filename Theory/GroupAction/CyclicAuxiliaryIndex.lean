module

public import Theory.GroupAction.CyclicQuotientRestrictionBound
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# A cyclic commutator bound from an auxiliary centralizing subgroup

Suppose B and C normalize one another, B/O₂(B) is abelian, and an element
t normalizing B centralizes C/O₂(C). Then the order of [B,⟨t⟩] modulo
its intrinsic two-core is at most [BX : CO₂(B)]. The auxiliary C need
not lie in B or X. Intersect CO₂(B) with B, use the displacement bound
on the abelian quotient, and absorb its two-group kernel into the
intrinsic core of the full commutator.

Source application: Aschbacher–Smith 13.8.20, printed p.954/PDF p.971.
This argument neither assumes nor produces an involution in place of t.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupAction.CyclicAuxiliaryIndex
variable {G : Type*} [Group G] [Finite G]

/-- The source index bounds the full cyclic commutator with its own core. -/
theorem commutator_twoCore_card_le (B C X : Subgroup G)
    (hBC : B ≤ normalizer (C : Set G)) (hCB : C ≤ normalizer (B : Set G))
    (habelian : ⁅B, B⁆ ≤ B.pCoreIn 2)
    (t : G) (htB : t ∈ normalizer (B : Set G))
    (hCt : ⁅C, zpowers t⁆ ≤ C.pCoreIn 2) :
    let D : Subgroup G := ⁅B, zpowers t⁆
    Nat.card (D ⧸ pCore 2 D) ≤
      (C ⊔ B.pCoreIn 2).relIndex (B ⊔ X) := by
  let P := B.pCoreIn 2
  let A := B ⊓ (C ⊔ P)
  let D := ⁅B, zpowers t⁆
  have hBP : B ≤ normalizer (P : Set G) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hCP : C ≤ normalizer (P : Set G) :=
    hCB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hDB : D ≤ B := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr htB)
  have hcore : B ⊓ C.pCoreIn 2 ≤ P :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 C).to_le inf_le_right) inf_le_left
      ((le_inf B.le_normalizer
        (hBC.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))).trans
          inf_normalizer_le_normalizer_inf)
  have htP : zpowers t ≤ normalizer (P : Set G) := zpowers_le.mpr
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B) htB)
  have hPt : ⁅P, zpowers t⁆ ≤ P := le_normalizer_iff_commutator_le_left.mp htP
  have hAt : ⁅A, zpowers t⁆ ≤ P := by
    apply commutator_le.mpr
    intro a ha s hs
    have ha' : a ∈ (C : Set G) * (P : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right C P hCP]
      exact ha.2
    obtain ⟨c, hc, p, hp, rfl⟩ := ha'
    have hcB : c ∈ B := (mul_mem_cancel_right (pCoreIn_le 2 B hp)).mp ha.1
    have hcP : ⁅c, s⁆ ∈ P := hcore
      ⟨hDB (commutator_mem_commutator hcB hs),
        hCt (commutator_mem_commutator hc hs)⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact P.mul_mem
      (le_normalizer_iff.mp hBP c hcB _ (hPt (commutator_mem_commutator hp hs))) hcP
  have hPN : (P.subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 B)).mpr hBP
  have hbound := quotient_commutator_relIndex_le_mul_of_restriction
    B A P P inf_le_left (pCoreIn_le 2 B) (pCoreIn_le 2 B) hPN habelian t htB hAt
  have hPP : P.relIndex P = 1 := relIndex_self _
  rw [hPP, mul_one] at hbound
  have hnormalD : (P.subgroupOf D).Normal := by
    refine ⟨?_⟩
    intro p hp d
    exact le_normalizer_iff.mp hBP d.val (hDB d.property) p.val hp
  have hPD : P.subgroupOf D ≤ pCore 2 D :=
    le_sSup ⟨hnormalD, (isPGroup_pCoreIn 2 B).comap_subtype⟩
  have hcard : Nat.card (D ⧸ pCore 2 D) ≤ P.relIndex D := by
    rw [← index_eq_card]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (P.subgroupOf D).index_ne_zero_of_finite)
      (index_dvd_of_le hPD)
  calc
    Nat.card (D ⧸ pCore 2 D) ≤ P.relIndex D := hcard
    _ ≤ P.relIndex (D ⊔ P) := relIndex_le_of_le_right le_sup_left (P.subgroupOf (D ⊔ P)).index_ne_zero_of_finite
    _ ≤ A.relIndex B := hbound
    _ = (C ⊔ P).relIndex B := inf_relIndex_left _ _
    _ ≤ (C ⊔ P).relIndex (B ⊔ X) :=
      relIndex_le_of_le_right le_sup_left ((C ⊔ P).subgroupOf (B ⊔ X)).index_ne_zero_of_finite

end Theory.GroupAction.CyclicAuxiliaryIndex
