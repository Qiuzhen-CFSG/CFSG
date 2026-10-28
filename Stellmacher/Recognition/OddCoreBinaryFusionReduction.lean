module
public import Stellmacher.Recognition.OddCoreSylow
public import Theory.GroupTheory.StrongEmbedding

/-!
# The remaining normalizers in binary odd-core fusion

Let A have elementary binary rank at least three in a Sylow subgroup S,
and let R be its nontrivial odd-core closure in a nonsolvable simple N₂
group. If N(R) is not strongly embedded, some nontrivial Q ≤ S has an
escaping normalizer. Such Q contains no elementary subgroup of order at
least eight. This isolates the cases not covered by Sylow control.

We also control the normalizer of an elementary subgroup E of order at
least four whenever its centralizer in S contains an elementary subgroup
of order at least eight. That subgroup connects E to A in the actual
commuting graph.

The elementary normalizer control is the closure version of GLS4,
Lemma 18.3(a) (`refs/KGroup/GLS4/Chapter2.tex`). The remaining reductions
isolate the binary fusion step discussed after GLS2, Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`). They do not assert the additional fusion
or uniqueness theorem needed for strong embedding.
-/

namespace Stellmacher.Recognition

/-- An elementary subgroup whose centralizer in S has elementary rank at
least three belongs to the controlled component. -/
public theorem normalizer_elementary_le_normalizer_oddCoreClosure_of_large_centralizer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A E B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hBS : B ≤ S)
    (hA : 8 ≤ Nat.card A) (hE : 4 ≤ Nat.card E) (hB : 8 ≤ Nat.card B)
    (hBE : B ≤ Subgroup.centralizer (E : Set G)) :
    Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have hAB := Subgroup.elementaryCommutingConnected_of_le_twoGroup
    (S : Subgroup G) A B S.isPGroup' hA hB hAS hBS
  have hBEpath : Subgroup.ElementaryCommutingConnected 2 B E :=
    Subgroup.ElementaryCommutingAdjacent.connected
      ⟨inferInstance, by norm_num; omega, inferInstance, by norm_num; omega, hBE⟩
  rw [oddCoreClosure_eq_of_connected hN (hAB.trans hBEpath)]
  exact normalizer_le_normalizer_involutionOddCoreClosure E

/-- Failure of strong embedding leaves an escaping normalizer only at
elementary rank at most two. -/
public theorem exists_smallRank_normalizer_escape_of_not_stronglyEmbedded
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥)
    (hnot : ¬ IsStronglyEmbedded
      (Subgroup.normalizer (involutionOddCoreClosure A : Set G))) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Q ≤ (S : Subgroup G) ∧
      (∀ B : Subgroup G, IsElementaryAbelian 2 B → B ≤ Q → Nat.card B < 8) ∧
      ¬ Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hS
    have hAbot : A = ⊥ := le_bot_iff.mp (hS ▸ hAS)
    simp [hAbot] at hA
  have hproper := ne_of_lt (oddCore_component_normalizer hns hN A hA hR).1
  obtain ⟨Q, hQ, hQp, hQS, hescape⟩ :=
    exists_twoSubgroup_le_sylow_normalizer_not_le_of_not_stronglyEmbedded
      S hSne (Subgroup.normalizer (involutionOddCoreClosure A : Set G))
      hproper (sylow_le_normalizer_oddCoreClosure hN S A hAS hA) hnot
  refine ⟨Q, hQ, hQp, hQS, ?_, hescape⟩
  intro B hBe hBQ
  let _ := hBe
  by_contra hB
  exact hescape (normalizer_le_normalizer_oddCoreClosure_of_le_sylow
    hN S A Q B hAS hQS hBQ hA (by omega))

/-- The remaining small-rank normalizer statement suffices for the binary
strong-embedding endpoint. Its fusion hypothesis is explicit. -/
public theorem isStronglyEmbedded_normalizer_oddCoreClosure_of_smallRank_control
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥)
    (hsmall : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ (S : Subgroup G) →
      (∀ B : Subgroup G, IsElementaryAbelian 2 B → B ≤ Q → Nat.card B < 8) →
      Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    IsStronglyEmbedded (Subgroup.normalizer (involutionOddCoreClosure A : Set G)) := by
  by_contra hnot
  obtain ⟨Q, hQ, hQp, hQS, hQr, hescape⟩ :=
    exists_smallRank_normalizer_escape_of_not_stronglyEmbedded
      hns hN S A hAS hA hR hnot
  exact hescape (hsmall Q hQ hQp hQS hQr)

end Stellmacher.Recognition
