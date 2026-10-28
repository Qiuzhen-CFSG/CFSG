module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.CComponent.CommutatorDichotomy

/-!
# The containing component in the contrary two-core branch

Normalize O₂(⟨K₀,T⟩). Simplicity and the genuine QTKE hypothesis give the
SQTK normalizer, and odd-prime ranks descend through its two-core quotient.
Lemma 1.2.5 constructs the unique containing C-component. Lemma 1.2.6 puts
that component in L(G,T), with actual Sylow subgroups and relative normality.

A.3.3(7) is supplied by its checked general commutator theorem. The full
earlier A.3.9(1) remains an explicit input. No containing
component or SQTK quotient is assumed. Source: Aschbacher–Smith,
Lemma 13.6.16(1), combined 1 March 2004 manuscript, printed p.930.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual containing C-component in the normalizer of the contrary
nontrivial two-core. The only component-existence inputs are the earlier
universal A.3.9(1); A.3.3(7) and the SQTK quotient are discharged here. -/
theorem containing_component_of_twoCore_ne_bot {𝒦 : GroupClass.{u}}
    (hA39 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X)
    (hG : IsSimpleQTKE 𝒦 G) (T : Sylow 2 G) (v : G) (K₀ : Subgroup G)
    (hK₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hcore : (K₀ ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥) :
    ∃ K₂ : Subgroup G,
      K₂ ∈ Chapter1.cComponentsIn
        (normalizer ((K₀ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) ∧
      K₀ ≤ K₂ ∧ K₂ ∈ Chapter1.L G (T : Subgroup G) ∧
      ∀ D ∈ Chapter1.cComponentsIn
        (normalizer ((K₀ ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)),
        K₀ ≤ D → D = K₂ := by
  let H := K₀ ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let N := normalizer (Q : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hTN : (T : Subgroup G) ≤ N := le_sup_right.trans hHN
  have hK₀N : K₀ ≤ N := le_sup_left.trans hHN
  have hRN : Tv (T : Subgroup G) v ≤ N := inf_le_left.trans hTN
  let S := T.subtype hTN
  have hRS : (Tv (T : Subgroup G) v).subgroupOf N ≤ (S : Subgroup N) := by
    intro x hx
    exact hx.1
  have hi : ((Tv (T : Subgroup G) v).subgroupOf N).relIndex (S : Subgroup N) = 2 := by
    change ((Tv (T : Subgroup G) v).subgroupOf N).relIndex
      ((T : Subgroup G).subgroupOf N) = 2
    rw [relIndex_subgroupOf hTN, hidx]
  have hlocal : K₀.subgroupOf N ∈ Chapter1.L N ((Tv (T : Subgroup G) v).subgroupOf N) :=
    (Chapter1.mem_LIn_iff_subgroupOf hRN hK₀N).mp ⟨hK₀N, hK₀.2⟩
  have hNQ : IsSQTK 𝒦 N := hG.twoLocal_sqtk
    ⟨Q, hcore, isPGroup_pCoreIn 2 H, rfl⟩
  have hQ : IsSQTK 𝒦 (N ⧸ pCore 2 N) := by
    refine ⟨?_, hNQ.isKGroup.quotient (pCore 2 N)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 N) pCore_isPGroup).trans
      (hNQ.stronglyQuasithin p hp ho)
  have hu := Chapter1.Section02.lemma_1_2_5_of_A_3_3_7_of_A_3_9
    (fun X _ _ B D hB => hB.commutator_le_radical_or_eq_iSup_conjugates D)
    hA39 hQ S hRS hi hlocal
  obtain ⟨K₂, ⟨hK₂, hle⟩, huniq⟩ :=
    (Chapter1.existsUnique_cComponentsIn_iff hK₀N).mp hu
  have hNH : N ∈ Chapter1.H G := by
    have hQN : Q ≤ N := Q.le_normalizer
    have hQQ : Q ≤ N.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hQN le_rfl
    exact fun he => hcore (bot_unique (he ▸ hQQ))
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) N :=
    ⟨S, by simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTN]⟩
  refine ⟨K₂, hK₂, hle, Chapter1.mem_L_of_cComponent hNH hSyl hK₂.1 hK₂.2, ?_⟩
  exact fun D hD hKD => huniq D ⟨hD, hKD⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
