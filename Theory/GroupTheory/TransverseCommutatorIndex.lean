module
public import Mathlib.GroupTheory.Index
public import Theory.GroupTheory.CommutatorPreimage

/-!
# A transverse subgroup improves a relative-index bound

If C is normalized by a finite subgroup A and D contains both A intersect C
and a subgroup Z of A, then |A:D| times |Z:C intersect Z| is at most
|A:A intersect C|. Work inside A, where C intersect A is normal, and apply
the quotient index formula to (A intersect C) join Z.

The commutator-preimage specialization gives the fixed-space estimate for
paired critical orbits in MS93 (3.6), printed p.871. It requires finiteness
only of A, so it applies inside the infinite free amalgam.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A normal intersection and a subgroup transverse to it improve an index
bound by the exact transverse relative index. -/
theorem transverse_relIndex_mul_le (A C Z D : Subgroup G) [Finite A]
    (hZA : Z ≤ A) (hAC : A ≤ normalizer (C : Set G))
    (hCD : A ⊓ C ≤ D) (hZD : Z ≤ D) :
    C.relIndex Z * D.relIndex A ≤ C.relIndex A := by
  let C0 := C.subgroupOf A
  let Z0 := Z.subgroupOf A
  let D0 := D.subgroupOf A
  let : C0.Normal := by
    constructor
    intro c hc a
    exact le_normalizer_iff.mp hAC a a.property c hc
  have hsup : C0 ⊔ Z0 ≤ D0 := by
    refine sup_le ?_ ?_
    · intro c hc
      exact hCD ⟨c.property,hc⟩
    · intro z hz
      exact hZD hz
  have hi : D0.index ≤ (C0 ⊔ Z0).index := Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := C0 ⊔ Z0))) (index_dvd_of_le hsup)
  have he : C0.relIndex (C0 ⊔ Z0) * (C0 ⊔ Z0).index = C0.index :=
    relIndex_mul_index le_sup_left
  have hz : C0.relIndex (C0 ⊔ Z0) = C.relIndex Z := by
    rw [relIndex_sup_left]
    exact relIndex_subgroupOf hZA
  rw [hz] at he
  exact (Nat.mul_le_mul_left _ hi).trans_eq he

/-- A commutator centralizer modulo Z contains both the normalized
intersection A∩C and Z, giving the same transverse index gain. -/
theorem commutatorPreimage_relIndex_mul_le (A B C Z : Subgroup G) [Finite A]
    (hZA : Z ≤ A) (hAC : A ≤ normalizer (C : Set G))
    (hcomm : ⁅A ⊓ C,B⁆ ≤ Z) (hZB : ⁅Z,B⁆ ≤ Z) :
    C.relIndex Z * (commutatorPreimage A B Z).relIndex A ≤ C.relIndex A := by
  exact transverse_relIndex_mul_le A C Z _ hZA hAC
    (le_commutatorPreimage inf_le_left hcomm) (le_commutatorPreimage hZA hZB)
end Subgroup
