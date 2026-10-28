module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Component
public import Theory.GroupTheory.PerfectSmallNormalizerAction

/-!
# Centralizers in the original HS overgroup

After U=O₂(K), faithfulness of the hatted action identifies C_K(U)=Z(U).
Perfectness makes K centralize its cyclic center and kills the second
commutator with C_H(U). Thus C_T(U)=C_T(K). The unique maximal two-local
overgroup of LT then forces C_T(L)=1: otherwise it would contain K and
hence the escaping point centralizer H.

Source: Aschbacher--Smith, proof of 14.3.33, printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal centralizer inside K is exactly the embedded center of U. -/
theorem component_centralizer_closure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    K ⊓ centralizer (F.U : Set G) = F.ZU := by
  let := h.chosen.elementary
  have hcore := component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU
  have hUK : F.U ≤ K := hcore ▸ pCoreIn_le 2 K
  rw [ZU, centerIn_eq_inf_centralizer]
  apply le_antisymm ?_ (inf_le_inf hUK le_rfl)
  rintro x ⟨hxK, hxC⟩
  refine ⟨?_, hxC⟩
  have hxker : (⟨x, hKH hxK⟩ : F.H) ∈ F.uhatAction.ker := by
    apply (F.mem_uhatAction_ker_iff _).mpr
    intro u hu
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hxC u hu).symm]
    exact one_mem _
  have hxQ : x ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype (s.kernel ▸ hxker)
  exact hcore.symm ▸ (inf_pCoreIn_le_of_le 2 hKH ⟨hxK, hxQ⟩)

/-- Perfectness identifies the two original Sylow centralizers. -/
theorem sylow_centralizer_closure_eq_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    (T : Subgroup G) ⊓ centralizer (F.U : Set G) =
      (T : Subgroup G) ⊓ centralizer (K : Set G) := by
  let := h.chosen.elementary
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have hnormal := (component_residual F s K hKH hK hKT).1
  have hHK : F.H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hnormal
  have hUK := (component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU).le.trans
    (pCoreIn_le 2 K)
  have hz : ⁅K, F.ZU⁆ = ⊥ := by
    obtain ⟨e⟩ := center_model F s
    apply commutator_eq_bot_of_perfect_normalizer_card_le_four
      K F.ZU (hKH.trans F.H_normalizes_ZU)
    exact le_of_eq ((Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4))
  have hc : F.H ⊓ centralizer (F.U : Set G) ≤ centralizer (K : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    have hcomm : ⁅F.H ⊓ centralizer (F.U : Set G), K⁆ ≤ F.ZU := by
      rw [← component_centralizer_closure h structural alternatives F s hne K hKH hK hKT hU]
      apply le_inf (le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hHK))
      exact (commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hKH.trans ((le_normalizer_conjugateSpanBy V F.H).trans (normalizer_le_normalizer_centralizer _))))
    exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans_eq
      ((commutator_comm _ _).trans hz))
  exact le_antisymm (le_inf inf_le_left ((inf_le_inf (F.invariant 1) le_rfl).trans hc))
    (inf_le_inf_left _ (centralizer_le hUK))

/-- The original ambient escape and uniqueness force C_T(L)=1. -/
theorem sylow_actor_centralizer_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  let := h.chosen.elementary
  obtain ⟨K, hKH, hK, hKT, hU, _⟩ := s.component
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  by_contra hn
  have hLC : L ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      ((h.sylow_normalizes_at structural).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hNC : normalizer (C : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hLN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hLN⟩)
    · exact T.isPGroup'.to_le inf_le_left
    · exact hn
    · exact sup_le hLC hTC
  have hCK : C ≤ centralizer (K : Set G) := by
    have hh : C ≤ (T : Subgroup G) ⊓ centralizer (F.U : Set G) :=
      inf_le_inf_left _ (centralizer_le (closure_le_actor h structural alternatives F s hne))
    rw [sylow_centralizer_closure_eq_component h structural alternatives F s hne K hKH hK hKT hU] at hh
    exact hh.trans inf_le_right
  have hKN : K ≤ normalizer (L : Set G) :=
    (le_centralizer_iff.mp hCK).trans ((Subgroup.centralizer_le_normalizer _).trans hNC)
  apply (h.point_mem_Hz_at F alternatives).2.2
  rw [hKT]
  exact sup_le hKN (h.sylow_normalizes_at structural)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
