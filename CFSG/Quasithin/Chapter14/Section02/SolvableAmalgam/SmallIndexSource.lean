module
public import Theory.GroupTheory.SylowSmallIndexModels
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source

/-!
# Small Sylow-index input to the original 14.2.20 amalgam

The actual 14.2.2(7) Sylow-normalizer bound excludes a normal Sylow in
an outside member of H(T). Index three or five therefore gives precisely
S₃, D₁₀, or the concrete Sz(2) after factoring out the two-core. Prime
index makes this same subgroup minimal outside M. Applying the original
amalgam construction gives F.1.1 on the literal pair (H, YT), including
its intersection, normalizers, and central involution.

These are the local inputs in the proof of Aschbacher–Smith 14.3.5,
printed p.991. The global recognition in 14.2.20 remains a separate theorem.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem outside_prime_index_minimal (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter1.HOver G (T : Set G)) (hout : ¬ H ≤ M)
    (hi : ((T : Subgroup G).relIndex H).Prime) :
    H ∈ Chapter3.HStar (T : Subgroup G) M := by
  refine ⟨⟨hH,hout⟩,?_⟩
  intro Y hY hYH
  have he := relIndex_mul_relIndex (T : Subgroup G) Y H hY.1.2 hYH
  have hp : ((T : Subgroup G).relIndex Y * Y.relIndex H).Prime := he.symm ▸ hi
  rcases Nat.prime_mul_iff.mp hp with ⟨_,h⟩ | ⟨_,h⟩
  · exact relIndex_eq_one.mp h
  · exact (hY.2 ((relIndex_eq_one.mp h).trans hTM)).elim

/-- Original small-index outside subgroups supply the actual 14.2.20 quotient models. -/
theorem source_small_index_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G)) (hout : ¬ H ≤ M)
    (hi : (T : Subgroup G).relIndex H = 3 ∨ (T : Subgroup G).relIndex H = 5) :
    H ∈ Chapter3.HStar (T : Subgroup G) M ∧ SmallSolvableModel (H ⧸ pCore 2 H) := by
  have hN : normalizer (T : Set G) ≤ M :=
    (source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e).trans inf_le_left
  have hnot : ¬ ((T : Subgroup G).subgroupOf H).Normal := by
    intro hn
    exact hout (((normal_subgroupOf_iff_le_normalizer hH.2).mp hn).trans hN)
  let S := T.subtype hH.2
  have hproper : pCore 2 H < (S : Subgroup H) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
    intro he
    apply hnot
    change (S : Subgroup H).Normal
    rw [←he]
    infer_instance
  refine ⟨outside_prime_index_minimal T hM.1.2 hH hout
    (hi.elim (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)),?_⟩
  exact sylow_small_index_core_quotient S hi hproper

/-- The small-index branch constructs F.1.1 for its actual outside subgroup and YT. -/
theorem source_small_index_hypothesis_F_1_1
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G)) (hout : ¬ H ≤ M)
    (hi : (T : Subgroup G).relIndex H = 3 ∨ (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ChapterF.Source.HypothesisF11 ![H,X] (T : Subgroup G) ∧
      H ⊓ X = T ∧
      H ⊓ normalizer (T : Set G) = T ∧ X ⊓ normalizer (T : Set G) = T ∧
      (T : Subgroup G) ≤ normalizer (sourceResidual M Mc : Set G) ∧
      Nat.card (centralInvolutions T) = 2 ∧ H ≤ centralizer (centralInvolutions T : Set G) := by
  obtain ⟨hstar,hmodel⟩ := source_small_index_models hG T hempty hM hu hmany hcard e H hH hout hi
  exact source_hypothesis_F_1_1 hG T hempty hM hu hmany hcard e H hstar hmodel

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
