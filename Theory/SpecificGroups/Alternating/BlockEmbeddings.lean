module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Disjoint-block embeddings of alternating groups

Even permutations on disjoint blocks give an injective product homomorphism.
Extending by the identity embeds a smaller alternating group in a larger one.
For degrees at least two, the factorial order formula proves that increasing
the degree gives a proper subgroup.

Source: the permutation subgroup constructions used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma A.2.16, printed p.38.
-/

public section

open scoped IsMulCommutative

namespace alternatingGroup

/-- The product action on two disjoint blocks, relabelled by their sum of degrees. -/
def sumEmbedding (n m : ℕ) :
    alternatingGroup (Fin n) × alternatingGroup (Fin m) →*
      alternatingGroup (Fin (n + m)) :=
  ((finSumFinEquiv.permCongrHom.toMonoidHom).comp
    ((Equiv.Perm.sumCongrHom _ _).comp
      ((alternatingGroup (Fin n)).subtype.prodMap (alternatingGroup (Fin m)).subtype))).codRestrict _
        (by
          intro a
          rw [Equiv.Perm.mem_alternatingGroup]
          change Equiv.Perm.sign (finSumFinEquiv.permCongr (Equiv.sumCongr a.1.val a.2.val)) = 1
          rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
            Equiv.Perm.mem_alternatingGroup.mp a.1.property,
            Equiv.Perm.mem_alternatingGroup.mp a.2.property, one_mul])

/-- The action on both disjoint blocks is faithful. -/
theorem sumEmbedding_injective (n m : ℕ) : Function.Injective (sumEmbedding n m) := by
  intro a b h
  have h' := finSumFinEquiv.permCongrHom.injective (congrArg Subtype.val h)
  have h'' := Equiv.Perm.sumCongrHom_injective h'
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h''))
    (Subtype.ext (congrArg Prod.snd h''))

/-- Extend an even permutation to a larger degree by fixing the added letters. -/
noncomputable def degreeEmbedding {n m : ℕ} (h : n ≤ m) :
    alternatingGroup (Fin n) →* alternatingGroup (Fin m) :=
  ((finCongr (Nat.add_sub_of_le h)).altCongrHom.toMonoidHom).comp
    ((sumEmbedding n (m - n)).comp (MonoidHom.inl _ _))

/-- Extending even permutations by the identity is injective. -/
theorem degreeEmbedding_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (degreeEmbedding h) := by
  intro a b hab
  have hx := (finCongr (Nat.add_sub_of_le h)).altCongrHom.injective hab
  exact congrArg Prod.fst (sumEmbedding_injective n (m - n) hx)

/-- Increasing the degree gives a proper subgroup, when the smaller degree is at least two. -/
theorem degreeEmbedding_range_ne_top {n m : ℕ} (hn : 2 ≤ n) (hm : n < m) :
    (degreeEmbedding hm.le).range ≠ ⊤ := by
  intro htop
  have he := MonoidHom.ofInjective (degreeEmbedding_injective hm.le)
  have hc : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin m)) := by
    simpa [htop] using Nat.card_congr he.toEquiv
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (hn.trans hm.le)
  have hncard := two_mul_nat_card_alternatingGroup (α := Fin n)
  have hmcard := two_mul_nat_card_alternatingGroup (α := Fin m)
  simp only [Nat.card_perm, Nat.card_fin] at hncard hmcard
  have hf := Nat.factorial_lt_of_lt (by omega : 0 < n) hm
  omega

end alternatingGroup

