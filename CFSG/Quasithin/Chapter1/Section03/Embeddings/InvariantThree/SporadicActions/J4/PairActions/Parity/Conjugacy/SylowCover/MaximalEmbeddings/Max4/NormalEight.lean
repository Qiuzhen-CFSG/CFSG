module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.NormalEight.Tables

/-!
# A normal elementary subgroup of order eight in literal J₄ max4

The subgroup consists of the identity and seven conjugates of the sixth power
of an explicit word in the two literal ATLAS program outputs. Kernel-checked
binary matrix products certify its multiplication table and both generator
conjugation permutations. The table proves exponent two and commutativity;
three first-row entries separate the eight words. Since the two program outputs
generate max4, their normalization proves normality relative to that subgroup.

This supplies precisely the normal-eight input of the maximal-embedding
reduction. Source context: the retained ATLAS J4G1-max4W1 program,
Kleidman–Wilson (1988), pp.484–510, and the Aschbacher (1986) citation in
Aschbacher–Smith, printed p.511/PDF p.528. No quotient, ambient order, or Sylow
rigidity hypothesis is used.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.NormalEight

/-- The eight certified words, as a subgroup of literal max4. -/
def eight : Subgroup max4Subgroup where
  carrier := Set.range element
  one_mem' := ⟨0, element_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨productIndex i j, (element_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    symm
    apply inv_eq_of_mul_eq_one_left
    exact element_sq i

/-- The table has exactly eight elements; its words are separated in the actual representation. -/
theorem card_eight : Nat.card eight = 8 := by
  let f : Fin 8 → eight := fun i => ⟨element i, ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact element_injective (congrArg Subtype.val h)
    · rintro ⟨g, ⟨i, rfl⟩⟩
      exact ⟨i, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 8)

/-- The multiplication table is commutative and every element squares to one. -/
theorem elementary_eight : IsElementaryAbelian 2 eight where
  toIsMulCommutative := IsMulCommutative.of_comm fun a b => by
    apply Subtype.ext
    obtain ⟨i, hi⟩ := a.property
    obtain ⟨j, hj⟩ := b.property
    change (a : max4Subgroup) * (b : max4Subgroup) = (b : max4Subgroup) * (a : max4Subgroup)
    rw [← hi, ← hj, element_comm]
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨g, ⟨i, rfl⟩⟩
    apply Subtype.ext
    exact (pow_two (element i)).trans (element_sq i)

private theorem normalizes_of_permutation (g : max4Subgroup) (p : Fin 8 → Fin 8)
    (hp : Function.Surjective p)
    (h : ∀ i, g⁻¹ * element i * g = element (p i)) :
    g ∈ Subgroup.normalizer (eight : Set max4Subgroup) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro a
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨p i, (h i).symm⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, rfl⟩ := hp j
    refine ⟨i, ?_⟩
    have he : g⁻¹ * element i * g = g⁻¹ * a * g := (h i).trans hj
    exact mul_left_cancel (mul_right_cancel he)

/-- Both actual program outputs normalize the eight, hence so does all of max4. -/
theorem normal_eight : eight.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← closure_x_y]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases (show g = x ∨ g = y from hg) with rfl | rfl
  · exact normalizes_of_permutation x actionX (by decide +kernel) element_conj_x
  · exact normalizes_of_permutation y actionY (by decide +kernel) element_conj_y

end Janko4.LocalStructure.SymmetricLinear.NormalEight

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- The literal max4 subgroup contains a normal elementary abelian subgroup of order eight. -/
theorem max4NormalElementaryEight : Max4NormalElementaryEight :=
  ⟨Janko4.LocalStructure.SymmetricLinear.NormalEight.eight,
    Janko4.LocalStructure.SymmetricLinear.NormalEight.normal_eight,
    Janko4.LocalStructure.SymmetricLinear.NormalEight.elementary_eight,
    Janko4.LocalStructure.SymmetricLinear.NormalEight.card_eight⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
