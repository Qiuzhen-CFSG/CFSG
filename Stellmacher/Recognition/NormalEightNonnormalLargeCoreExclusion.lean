module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative
public import Stellmacher.Recognition.NormalEightLargeCoreIndexTwo
public import Stellmacher.Recognition.NormalEightLargeCoreHigherIndexEight
public import Stellmacher.Recognition.NormalEightLargeCoreHigherIndexRankTwo
public import Stellmacher.Recognition.NormalEightLargeCoreRankTwoSection

/-!
# Exclusion of an actual extraspecial core of order thirty-two

The nonnormal image of the unique normal four makes the quotient core proper
in the quotient Sylow. Its index is a power of two, hence is two or at least
four. At higher index the intrinsic elementary-rank alternative covers both
extraspecial types: a core with elementary rank at most two, or one containing
an elementary eight. Such an eight is normal in the core but cannot be
normalized by the whole quotient Sylow.

The imported fusion and transfer results discharge the index-two and
higher-index elementary-eight exclusions. In the remaining branch, core-local
elementary rank at most two supplies inside-core weak closure and a
centralizing cyclic-four section, giving the final contradiction. The final
assembly excludes both extraspecial types under the normal-only hypotheses;
an arbitrary elementary eight is allowed.

Source: Janko–Thompson (1970), §4, printed pp.389–392.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- Nonnormality of the four image rules out index one; the remaining index
is two or at least four. No bound on arbitrary elementary subgroups is used. -/
public theorem omegaCorePreimage_index_eq_two_or_four_le
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    (omegaCorePreimage S).index = 2 ∨ 4 ≤ (omegaCorePreimage S).index := by
  have hone : (omegaCorePreimage S).index ≠ 1 := by
    rw [index_omegaCorePreimage]
    intro h
    have hle : pCore 2 (OmegaQuotient S) ≤ omegaQuotientSylow S :=
      pCore_isPGroup.le_sylow_of_normal _
    have heq := le_antisymm hle (relIndex_eq_one.mp h)
    exact omegaQuotientSylow_not_normal S W hW hunique hnormal
      (heq ▸ (inferInstance : (pCore 2 (OmegaQuotient S)).Normal))
  obtain ⟨n, hn⟩ := S.isPGroup'.index (omegaCorePreimage S)
  rcases n with _ | n
  · simp [hn] at hone
  · rcases n with _ | n
    · exact Or.inl (by simpa using hn)
    · right
      rw [hn]
      exact Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ n + 1 + 1)

/-- An elementary eight in the core is never normalized by the quotient
Sylow under the normal-only bound. -/
public theorem omegaQuotient_pCore_elementary_eight_not_sylow_normalized
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (E : Subgroup (pCore 2 (OmegaQuotient S))) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) :
    ¬ (omegaQuotientSylow S : Subgroup (OmegaQuotient S)) ≤
      normalizer (E.map (pCore 2 (OmegaQuotient S)).subtype : Set (OmegaQuotient S)) := by
  intro hnorm
  let : IsElementaryAbelian 2 (E.map (pCore 2 (OmegaQuotient S)).subtype) :=
    IsElementaryAbelian.map_subtype
  have hlt := omegaQuotient_sylow_normalized_elementary_card_lt_eight S hno
    (E.map (pCore 2 (OmegaQuotient S)).subtype)
    ((map_subtype_le E).trans (pCore_isPGroup.le_sylow_of_normal _)) hnorm
  rw [card_map_of_injective (pCore 2 (OmegaQuotient S)).subtype_injective, hE] at hlt
  omega

/-- The three ambient exclusions suffice, covering both extraspecial types.
The elementary-rank premise in the second branch concerns only the core. -/
public theorem omegaQuotient_large_core_false_of_three_exclusions
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindexTwo : (omegaCorePreimage S).index = 2 → False)
    (hrankTwo : 4 ≤ (omegaCorePreimage S).index →
      (∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
        IsElementaryAbelian 2 E → Nat.card E < 8) → False)
    (helementaryEight : 4 ≤ (omegaCorePreimage S).index →
      ∀ E : Subgroup (pCore 2 (OmegaQuotient S)), E.Normal →
        IsElementaryAbelian 2 E → Nat.card E = 8 →
          center (pCore 2 (OmegaQuotient S)) ≤ E → False) : False := by
  rcases omegaCorePreimage_index_eq_two_or_four_le S W hW hunique hnormal with hi | hi
  · exact hindexTwo hi
  · rcases IsExtraspecial.rank_two_or_normal_elementary_eight_of_card_thirty_two hH with
      hrank | ⟨E, hEn, hEe, hE, hZE⟩
    · exact hrankTwo hi hrank
    · exact helementaryEight hi E hEn hEe hE hZE

/-- The completed index-two and quaternion–quaternion exclusions leave only
the higher-index branch with core-local elementary rank at most two. -/
public theorem omegaQuotient_large_core_false_of_rank_two_exclusion
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hrankTwo : 4 ≤ (omegaCorePreimage S).index →
      (∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
        IsElementaryAbelian 2 E → Nat.card E < 8) → False) : False := by
  apply omegaQuotient_large_core_false_of_three_exclusions S W hW hunique hnormal hH
  · exact large_core_index_two_false hns hN S A hA hnonab hZ hno W hW hunique hnormal hH
  · exact hrankTwo
  · intro hi E hEn hEe hE hZE
    let : E.Normal := hEn
    let : IsElementaryAbelian 2 E := hEe
    exact higherIndexEight_false_of_elementary_eight hns hN S A hA hnonab hZ hno
      W hW hunique hnormal hH hi E hE hZE

/-- Final assembly from the two remaining quaternion–dihedral inputs.
Both inputs concern only the higher-index, core-local-rank branch. The section
input may assume the outside fused involution supplied by the fusion input;
it does not depend on the proof of that input. -/
public theorem omegaQuotient_large_core_false_of_rank_two_fusion_and_sections
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hinside : 4 ≤ (omegaCorePreimage S).index →
      (∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
        IsElementaryAbelian 2 E → Nat.card E < 8) →
      ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
        t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z)
    (hsections : 4 ≤ (omegaCorePreimage S).index →
      (∀ E : Subgroup (pCore 2 (OmegaQuotient S)),
        IsElementaryAbelian 2 E → Nat.card E < 8) →
      ∀ z t : S, orderOf z = 2 → z ∈ center S → orderOf t = 2 →
        t ∉ omegaCorePreimage S → IsConj (z : G) (t : G) →
        ∃ (K : Subgroup S) (Z : Subgroup K) (_ : Z.Normal),
          IsCyclic (K ⧸ Z) ∧ Nat.card (K ⧸ Z) = 4 ∧
          Z ≤ (center S).comap K.subtype ∧ K ≤ centralizer (W : Set S) ∧
          t ∈ K ∧ omegaCorePreimage S ⊓ centralizer ({t} : Set S) ≤ W) : False := by
  apply omegaQuotient_large_core_false_of_rank_two_exclusion
    hns hN S A hA hnonab hZ hno W hW hunique hnormal hH
  intro hi hrank
  obtain ⟨z, t, hz, hzc, ht, hout, hzt⟩ :=
    large_core_rank_two_outside_conjugate_of_core_fusion hns S hZ (hinside hi hrank)
  obtain ⟨K, Z, hZn, hcyclic, hquot, hZK, hKW, htK, hfixed⟩ :=
    hsections hi hrank z t hz hzc ht hout hzt
  let : Z.Normal := hZn
  let : IsCyclic (K ⧸ Z) := hcyclic
  exact large_core_rank_two_false_of_centralizing_section hN S hZ hno W hW hH
    K Z hquot hZK hKW ⟨t, htK⟩ (by
      apply Subtype.ext
      change t ^ 2 = 1
      simpa only [ht] using pow_orderOf_eq_one t) hfixed

/-- An actual extraspecial quotient core of order thirty-two is impossible
under the normal-only elementary bound. This covers both extraspecial types,
using the core-local rank alternative only in the higher-index branch. -/
public theorem omegaQuotient_large_core_false
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32) : False := by
  exact omegaQuotient_large_core_false_of_rank_two_exclusion
    hns hN S A hA hnonab hZ hno W hW hunique hnormal hH
    (large_core_rank_two_false hns hN S hZ hno W hW hunique hH)

end Stellmacher.Recognition.NormalEightNonnormalImage
