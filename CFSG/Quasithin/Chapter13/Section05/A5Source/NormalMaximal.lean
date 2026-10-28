module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPairCompletion

/-!
# The full maximal local group in the original normal A₅ branch

The five-letter action of the module normalizer contains the original A₅
action. Its kernel is the module centralizer. Once the preceding normal-pair
argument identifies that centralizer with V, the index of LT in N_G(V)
divides two. Since LT contains the original Sylow two-subgroup, that index
is odd and hence one. This proves the remaining equality in 13.5.15(7).

Source: Aschbacher–Smith, 13.5.15(7) and the opening of 13.5.17,
printed pp.921–922. The preceding block and normal-pair source arguments
retain their genuine earlier embedding input.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

namespace Context
variable (d : Context T L V V₁ V₂ V₃)
include d

/-- The actual five-point action bounds the odd index of LT in its module
normalizer. Its only kernel input is the literal centralizer containment. -/
theorem module_normalizer_eq_local_of_centralizer_le
    (hC : centralizer (V : Set G) ≤ L ⊔ (T : Subgroup G)) :
    normalizer (V : Set G) = L ⊔ (T : Subgroup G) := by
  let N := normalizer (V : Set G)
  let J := L ⊔ (T : Subgroup G)
  have hJN : J ≤ N := sup_le d.chosen.normalizes d.flag.T_normalizes
  let f := d.flag.normalizerAction
  have hk : f.ker ≤ J.subgroupOf N := by
    intro x hx
    exact hC ((actor_eq_one_iff d.flag x).mp hx)
  have ha : alternatingGroup (Fin 5) ≤ (J.subgroupOf N).map f := by
    intro a ha
    obtain ⟨l,hl⟩ := d.flag.module.onto ⟨a,ha⟩
    refine ⟨⟨l,d.chosen.normalizes l.property⟩,mem_sup_left l.property,?_⟩
    exact (d.flag.action_agrees l _).trans (congrArg Subtype.val hl)
  have hdiv : (J.subgroupOf N).index ∣ 2 := by
    have hd := ((J.subgroupOf N).dvd_index_map hk).trans (index_dvd_of_le ha)
    simpa only [alternatingGroup.index_eq_two] using hd
  let S : Sylow 2 N := T.subtype d.flag.T_normalizes
  have hSJ : (S : Subgroup N) ≤ J.subgroupOf N := by
    intro x hx
    exact (show (T : Subgroup G) ≤ J from le_sup_right) hx
  have hodd : ¬ 2 ∣ (J.subgroupOf N).index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hSJ))
  have hi : (J.subgroupOf N).index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hi | hi
    · exact hi
    · exact (hodd (by rw [hi])).elim
  have ht : J.subgroupOf N = ⊤ := index_eq_one.mp hi
  apply le_antisymm ?_ hJN
  intro x hx
  have hm : (⟨x,hx⟩ : N) ∈ J.subgroupOf N := by rw [ht]; trivial
  exact hm

end Context

variable [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The original A₅ instance of all of 13.5.15(7), with the full
normalizer equality proved from the same source Context. -/
theorem normal_source13_5_15_seven :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      V = (normalizer (L : Set G)).pCoreIn 2 := by
  obtain ⟨hc,hN,hC⟩ := normal_maximal_core_eq_module d hA312 hH hU hn
  exact ⟨hN.symm.trans (d.module_normalizer_eq_local_of_centralizer_le
    (hC.le.trans (d.chosen.le_sylow.trans le_sup_right))),hc.symm⟩

/-- The module normalizer used in 13.5.17 is the original local product LT. -/
theorem normal_module_normalizer_eq_local :
    normalizer (V : Set G) = L ⊔ (T : Subgroup G) := by
  exact (normal_maximal_core_eq_module d hA312 hH hU hn).2.1.trans
    (normal_source13_5_15_seven d hA312 hH hU hn).1

end CFSG.Quasithin.Chapter13.Section05.A5Source
