module
public import Mathlib.GroupTheory.Nilpotent

/-!
# The index bound for trivial-intersection subgroups

In a finite group satisfying the normalizer condition, a TI-subgroup whose
index is at most its order is normal. If its normalizer were proper, the
normalizer condition would supply a distinct conjugate inside that normalizer.
Multiplication of the two disjoint conjugates gives the opposite order bound,
forcing the normalizer to be the whole group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, I.7.3,
printed p. 426. This isolates the normalizer-condition argument from the
source's tightly embedded subgroup setup.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem normal_of_trivial_intersections_of_index_le_card
    (hnc : NormalizerCondition G) (Q : Subgroup G)
    (hTI : ∀ g : G, g ∉ normalizer (Q : Set G) →
      Q ⊓ Q.map (MulAut.conj g).toMonoidHom = ⊥)
    (hindex : Q.index ≤ Nat.card Q) : Q.Normal := by
  apply normalizer_eq_top_iff.mp
  by_contra hn
  let N := normalizer (Q : Set G)
  obtain ⟨g, hgN, hg⟩ := SetLike.exists_of_lt (hnc N (lt_top_iff_ne_top.mpr hn))
  let R := Q.map (MulAut.conj g).toMonoidHom
  have hRN : R ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hgN x).mp (Q.le_normalizer hx)
  have hdisj : Disjoint Q R := disjoint_iff.mpr (hTI g hg)
  let f : Q × R → N := fun x => ⟨(x.1 : G) * (x.2 : G),
    N.mul_mem (Q.le_normalizer x.1.property) (hRN x.2.property)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact mul_injective_of_disjoint hdisj (congrArg Subtype.val hxy)
  have hcard := Nat.card_le_card_of_injective f hf
  have hRcard : Nat.card R = Nat.card Q :=
    card_map_of_injective (MulAut.conj g).injective
  rw [Nat.card_prod, hRcard] at hcard
  have hGcard : Nat.card G ≤ Nat.card N := by
    calc
      Nat.card G = Q.index * Nat.card Q := Q.index_mul_card.symm
      _ ≤ Nat.card Q * Nat.card Q := Nat.mul_le_mul_right _ hindex
      _ ≤ Nat.card N := hcard
  apply hn
  exact eq_top_of_card_eq N (le_antisymm (card_le_card_group N) hGcard)

end Subgroup
