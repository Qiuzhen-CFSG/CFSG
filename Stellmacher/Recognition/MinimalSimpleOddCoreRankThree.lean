module

public import Stellmacher.Recognition.MinimalSimpleOddCoreOvergroups
public import Stellmacher.Recognition.MinimalSimpleOddCoreSmallRank
public import Stellmacher.Recognition.OddCoreStrongEmbedding
public import Stellmacher.Recognition.OddCoreSylow
public import Theory.GroupTheory.StrongEmbedding

/-!
# The minimal-simple reduction for a rank-three odd-core closure

This module records the part of the minimal-simple route that follows from the
completed signalizer functor and does not hide the remaining uniqueness
argument.  If the closure attached to a rank-three elementary abelian
subgroup is nontrivial, its normalizer is a proper solvable subgroup.  A Sylow
two-subgroup containing the actor is contained in that normalizer.  Thus every
maximal overgroup of the normalizer is a proper solvable overgroup containing
the same Sylow subgroup. The recovered internal-control theorem now shows
that the normalizer itself is maximal. The missing Thompson uniqueness step
must exclude a small-rank normalizer which, together with this maximal
subgroup, generates the whole group.

For every proper overgroup M of the normalizer we prove
R ≤ O₂′(M) ≤ N_G(R), and F(M) ≤ N_G(R). Equality of a proper overgroup
with N_G(R) uses the separate quotient and fusion argument in
`MinimalSimpleOddCoreSmallRank`, not these containments alone. The
strong-embedding obstruction leaves a nontrivial two-subgroup of elementary
rank at most two whose normalizer escapes N_G(R).

Source: the Bender method and signalizer connectivity in GLS2, Chapter F,
§§19 and 21–22. These reductions isolate the remaining uniqueness step;
they do not assert the unconditional vanishing conclusion.
-/

namespace Stellmacher.Recognition

open Theory.GroupTheory

universe u

/-- A nontrivial rank-three odd-core closure in a minimal-simple group has a
proper solvable normalizer containing a Sylow two-subgroup of the ambient
group. -/
public theorem minimalSimple_oddCore_rankThree_reduction
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) :
    involutionOddCoreClosure A = ⊥ ∨
      ∃ (M : Subgroup G) (S : Sylow 2 G),
        M < ⊤ ∧ Group.IsSolvable M ∧
          M = Subgroup.normalizer (involutionOddCoreClosure A : Set G) ∧
          A ≤ S ∧ (S : Subgroup G) ≤ M := by
  by_cases hR : involutionOddCoreClosure A = ⊥
  · exact Or.inl hR
  · right
    let hN := hG.isNTwoGroup
    let _ := hG.isSimpleGroup
    have hM := oddCore_component_normalizer hG.not_isSolvable hN A hA hR
    obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
    have hSM := sylow_le_normalizer_oddCoreClosure hN S A hAS hA
    let M := Subgroup.normalizer (involutionOddCoreClosure A : Set G)
    refine ⟨M, S, hM.1, ?_, rfl, hAS, hSM⟩
    exact hG.solvable_of_lt M hM.1

/-- Any nontrivial closure leaves an escaping two-subgroup of elementary
rank at most two. All higher-rank normalizers are already controlled. -/
public theorem minimalSimple_oddCore_exists_small_rank_escape
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (S : Sylow 2 G) (hAS : A ≤ S) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Q ≤ S ∧
      ¬ Subgroup.normalizer (Q : Set G) ≤
        Subgroup.normalizer (involutionOddCoreClosure A : Set G) ∧
      ∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B → Nat.card B < 8 := by
  let _ := hG.isSimpleGroup
  have hN := hG.isNTwoGroup
  have hproper := (oddCore_component_normalizer hG.not_isSolvable hN A hA hR).1
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hS
    have hAbot : A = ⊥ := bot_unique (hAS.trans_eq hS)
    have hcard : Nat.card A = 1 := by rw [hAbot]; exact Subgroup.card_bot
    omega
  obtain ⟨Q, hQ, hQtwo, hQS, hQN⟩ :=
    exists_twoSubgroup_le_sylow_normalizer_not_le_of_not_stronglyEmbedded
      S hSne _ (ne_of_lt hproper)
      (sylow_le_normalizer_oddCoreClosure hN S A hAS hA)
      (not_isStronglyEmbedded_normalizer_involutionOddCoreClosure hN A hA)
  refine ⟨Q, hQ, hQtwo, hQS, hQN, ?_⟩
  intro B hBQ hB
  let _ := hB
  by_contra hsmall
  exact hQN (normalizer_le_normalizer_oddCoreClosure_of_le_sylow
    hN S A Q B hAS hQS hBQ hA (by omega))

/-- A nontrivial closure forces a small-rank two-subgroup whose normalizer
generates the whole group together with the closure normalizer. The latter
is maximal by the proved internal-control theorem. -/
public theorem minimalSimple_oddCore_exists_generating_small_rank_escape
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) (S : Sylow 2 G) (hAS : A ≤ S) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Q ≤ S ∧
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) ⊔
        Subgroup.normalizer (Q : Set G) = ⊤ ∧
      ∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B → Nat.card B < 8 := by
  obtain ⟨Q, hQ, hQtwo, hQS, hQN, hsmall⟩ :=
    minimalSimple_oddCore_exists_small_rank_escape hG A hA hR S hAS
  refine ⟨Q, hQ, hQtwo, hQS, ?_, hsmall⟩
  by_contra hjoin
  exact hQN (minimalSimple_oddCore_normalizer_control_of_proper_join
    hG A Q hA (lt_top_iff_ne_top.mpr hjoin))

/-- The remaining small-rank normalizer control suffices for the desired
vanishing theorem. This is an explicit conditional assembly interface. -/
public theorem minimalSimple_oddCore_eq_bot_of_small_rank_control
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hcontrol : involutionOddCoreClosure A ≠ ⊥ →
      ∀ (S : Sylow 2 G), A ≤ S → ∀ Q : Subgroup G,
        Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ S →
        (∀ B : Subgroup G, B ≤ Q → IsElementaryAbelian 2 B → Nat.card B < 8) →
        Subgroup.normalizer (Q : Set G) ≤
          Subgroup.normalizer (involutionOddCoreClosure A : Set G)) :
    involutionOddCoreClosure A = ⊥ := by
  by_contra hR
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨Q, hQ, hQtwo, hQS, hQN, hsmall⟩ :=
    minimalSimple_oddCore_exists_small_rank_escape hG A hA hR S hAS
  exact hQN (hcontrol hR S hAS Q hQ hQtwo hQS hsmall)

end Stellmacher.Recognition
