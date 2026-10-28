module
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Fixed indices with relative kernel normality

For a finite binary conjugation section, the commutator preimage has index
two to the fixed codimension of the literal actor. Only the section and actor
need to normalize the coordinate kernel; neither ambient finiteness nor
normality in the whole ambient group is required. The proof maps the full
preimage onto the fixed space and cancels its cardinality in the index formula.

Source application: MS93 (3.6), printed p.871, for the two secondary orbits
in the free-amalgam group.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection

/-- The full fixed index under the two relative normalization hypotheses. -/
theorem fixed_index_of_relative_normalizers {G : Type*} [Group G]
    {S A Z : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) S V} [Finite A]
    (c : BinaryConjugationSection S A Z ρ)
    (P : Subgroup G) (hPS : P ≤ S)
    (hAZ : A ≤ normalizer Z) (hPZ : P ≤ normalizer Z) :
    (commutatorPreimage A P Z).relIndex A =
      2 ^ Representation.BinaryOffender.fixedCodim ρ (P.subgroupOf S) := by
  let : Finite V := Finite.of_surjective (fun u : A => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let C := commutatorPreimage A P Z
  let B : Subgroup (Multiplicative V) := AddSubgroup.toSubgroup'
    (Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S)).toAddSubgroup
  have hm : (C.subgroupOf A).map c.coordinates = B := by
    ext v
    change v.toAdd ∈ c.imageSpace C ↔ v.toAdd ∈
      Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S)
    rw [c.fixed_image_eq P hPS hAZ]
  have hz : Z ≤ C := le_commutatorPreimage c.kernel_le
    (le_normalizer_iff_commutator_le_left.mp hPZ)
  have hk : c.coordinates.ker ≤ C.subgroupOf A := by
    rw [c.kernel_eq]
    exact comap_mono hz
  have hi : B.index = C.relIndex A := by
    rw [←hm,index_map_eq _ c.onto hk]
    rfl
  have hc := B.card_mul_index
  have hB : Nat.card B = 2 ^ Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S)) := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf S))).trans
        (by rw [Nat.card_zmod])
  have hV : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
    exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)).trans
      (by rw [Nat.card_zmod])
  rw [hB,hV,←Representation.BinaryOffender.fixedCodim_add_finrank ρ
    (P.subgroupOf S),add_comm,pow_add] at hc
  exact hi.symm.trans (Nat.eq_of_mul_eq_mul_left (by positivity) hc)


end Representation.BinaryConjugationSection
