module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.ConjugateSpanOrder
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# The cubic residual of a nonnormal component orbit

The four actual nonnormal models of 1.2.1 identify the component orbit with
the prime-to-three residual. The two linear families use their existing rank
calculation, Suzuki is excluded by its order, and the Janko case uses its
trivial outer group. Every residual retains the original ambient subgroup.

Source: Aschbacher--Smith 1.2.1--2, printed pp.504--505.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem pair_eq_threeResidual_of_index
    {K : Subgroup G} (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hd : 3 ∣ Nat.card (K ⧸ pCore 2 K)) (t : G)
    (hn : (K ⊔ K.conjBy t).Normal)
    (hi : Nat.Coprime 3 (K ⊔ K.conjBy t).index) :
    K ⊔ K.conjBy t = primeToResidual 3 G := by
  let := hn
  let : Group.IsPerfect K := hK.perfect
  have hperfect : IsPPerfect 2 K := by
    intro N hN hquot
    let := hN
    have hs : Subsingleton (K ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have hKR : K ≤ primeToResidual 3 G := le_primeToResidual_of_eq_top 3 K
    (primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 K) pCore_isPGroup hperfect hd)
  refine le_antisymm (sup_le hKR ?_) (primeToResidual_le _ hi)
  rintro x ⟨k, hk, rfl⟩
  exact (inferInstance : (primeToResidual 3 G).Normal).conj_mem k (hKR hk) t

/-- All four actual nonnormal models of1.2.1 give the cubic orbit residual.
Positive three-rank excludes Suzuki; Janko's actual outer group is trivial. -/
theorem nonnormal_component_threeResidual
    {K : Subgroup G} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hi : (normalizer (K : Set G)).index = 2)
    (hd : 3 ∣ Nat.card (K ⧸ pCore 2 K)) (hr : primeRank 3 G ≤ 2)
    (hm : NonnormalCComponentModel (K ⧸ pCore 2 K)) :
    primeToResidual 3 G = conjugateSpanBy K ⊤ := by
  classical
  have hex : ∃ t : G, t ∉ normalizer (K : Set G) := by
    by_contra! h
    have hn : normalizer (K : Set G) = ⊤ := eq_top_iff.mpr (fun t _ => h t)
    rw [hn, index_top] at hi
    omega
  obtain ⟨t, ht⟩ := hex
  have hnorm := TwoOrbitThree.pair_normal_of_index_two K hi t ht
  have he : K ⊔ K.conjBy t = primeToResidual 3 G := by
    cases hm with
    | linear_even n hn he =>
      exact rankOne_pair_eq_primeToResidual_three hK hi t ht hd hr (Or.inl ⟨n, he⟩)
    | linear_prime p hp ho he =>
      exact rankOne_pair_eq_primeToResidual_three hK hi t ht hd hr (Or.inr ⟨p, hp, ho, he⟩)
    | suzuki m hm he =>
      obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv] at hd
      exact (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd).elim
    | janko he =>
      obtain ⟨e⟩ := he
      have hz : center (K ⧸ pCore 2 K) = ⊥ := by
        rcases (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top with h | h
        · exact h
        · exact (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K)
            (center_eq_top_iff.mp h)).elim
      have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
        let := Janko1.OuterCertificate.outer_subsingleton
        let : Subsingleton (MulAut.Outer (K ⧸ pCore 2 K)) :=
          (MulAut.outerCongr e).injective.subsingleton
        rw [Nat.card_unique]
        decide
      exact pair_eq_threeResidual_of_index hK hd t hnorm
        (TwoOrbitThree.outer_cComponent_pair_index_coprime_three hK hi t ht hz hd hr ho)
  rw [← he]
  apply le_antisymm
  · refine sup_le (le_conjugateSpanBy K ⊤) ?_
    rintro x ⟨k, hk, rfl⟩
    exact subset_closure ⟨t, mem_top t, k, hk, rfl⟩
  · let := hnorm
    apply conjugateSpanBy_le le_sup_left
    rw [normalizer_eq_top]

end CFSG.Quasithin.Chapter1.Section02
