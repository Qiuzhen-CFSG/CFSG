module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Complete
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# The starred solvable-family normalizer theorem

The complete adequate intrinsic embedding theorem makes each starred Xi
member normal in every maximal two-local overgroup of XT. Both the original
component alternatives and the retained Held alternative contradict the
defining star exclusion. Local characteristic two gives a nontrivial core,
and the general maximality argument identifies the unique overgroup with
N_G(X). No solvability or radical-family restriction is imposed.

Source: Aschbacher–Smith, Proposition 1.3.5 and Theorem 1.3.7, pp.511–512.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

theorem normal_of_XiStar_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {X M : Subgroup G} (hX : X ∈ XiStar G (T : Subgroup G))
    (hM : IsMaximalTwoLocal M) (hXM : X ⊔ (T : Subgroup G) ≤ M) :
    (X.subgroupOf M).Normal := by
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have hT : IsSylowIn 2 (T : Subgroup G) M := by
    refine ⟨T.subtype hTM, ?_⟩
    simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM]
  obtain ⟨p, hp, ho, hq⟩ := hX.1.odd_quotient
  let : Fact p.Prime := ⟨hp⟩
  let d := localInput_of_mem_Xi hX.1 hT hXM ho hq (default : Sylow p X)
  rcases d.adequate_knownSimple (hG.twoLocal_sqtk hM.1) hT with hn | ⟨L, hL, hqL, hXL, _⟩
  · exact hn
  · have hLL := (lemma_1_2_6 T ⟨mem_H_of_isTwoLocal hM.1, hTM⟩).1 hL
    exact (hX.2 L hLL.2 hqL (sup_le
      (hXL.trans (componentOrbit_le_sup L (T : Subgroup G))) le_sup_right)).elim

theorem normalizer_unique_of_XiStar_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ XiStar G (T : Subgroup G)) :
    IsMaximalTwoLocal (normalizer (X : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} =
        {normalizer (X : Set G)} := by
  have hcore : X.pCoreIn 2 ≠ ⊥ := hX.1.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (hG.evenCharacteristic T))
  apply Section03.normalizer_unique_of_normal_in_maximalTwoLocals X T hX.1.invariant
    (fun he => hcore (by change (pCore 2 X).map X.subtype = ⊥; rw [he, Subgroup.map_bot]))
  exact fun M hM hXM => normal_of_XiStar_knownSimple hG T hX hM hXM

end CFSG.Quasithin.Chapter1.XiEmbedding
