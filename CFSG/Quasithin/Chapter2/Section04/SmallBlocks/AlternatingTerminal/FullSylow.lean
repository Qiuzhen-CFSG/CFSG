module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LieRows
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Mathieu
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.SmallRows
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.Bender
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.SporadicOrder
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import Theory.GroupTheory.SylowLocalCore

/-!
# The single deleted-five block at a full component Sylow

A quasisimple SQTK group of Sylow order at most 256 cannot contain a local
alternating-five block normalized by that Sylow, with its order-sixteen
module and disjoint central kernel. The literal central quotient preserves
the block and its local condition. The proved Theorem C supplies the model:
small rows fail order or rank, large sporadics fail the Sylow bound, and
canonical rank-two and Mathieu local obstructions contradict full-Sylow
locality. Restricting to the actual ordinary component gives the final
inclusion consumer, with no separate classification premise.

Source: Aschbacher--Smith 2.4.29, printed p.545, the nontrivial C_T(L) case.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
open ChapterC ChapterA.Section03.SourceEmbeddings
open Chapter13.Section05.NormalBranch.DeletedFive
variable {X : Type*} [Group X] [Finite X]

private theorem no_invariant_escape (T : Sylow 2 X) (A N : Subgroup X)
    (hlocal : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X)) (hAN : A ≤ N)
    (hInv : ∀ a : MulAut X, ((blockU A).map A.subtype).map a.toMonoidHom =
      (blockU A).map A.subtype → N.map a.toMonoidHom = N)
    (hbad : ∀ Q : Sylow 2 N, A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q) :
    False := by
  have hTN : (T : Subgroup X) ≤ normalizer (N : Set X) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply hInv
    exact mem_normalizer_iff_map_conj_eq.mp
      ((hn.trans (normalizer_le_normalizer_characteristic_image A (blockU A))) ht)
  let J := N ⊔ (T : Subgroup X)
  have hNJ : N ≤ J := le_sup_left
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup X) ≤ J from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes hNJ
    (sup_le N.le_normalizer hTN)
  have hQT : (Q : Subgroup N) = (T : Subgroup X).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hQ,subgroupOf_map_subtype]
    have ht : ((T.subtype (show (T : Subgroup X) ≤ J from le_sup_right) : Sylow 2 J) : Subgroup J).map J.subtype = T :=
      map_subgroupOf_eq_of_le le_sup_right
    rw [ht,inf_comm]
  exact hbad Q (hQT.symm ▸ local_restrict hlocal hAN)

omit [Finite X] in
private theorem no_normalizer_escape (T : Sylow 2 X) (A : Subgroup X)
    (hlocal : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (hbad : ∀ Q : Sylow 2 (normalizer ((blockU A).map A.subtype : Set X)),
      A.subgroupOf (normalizer ((blockU A).map A.subtype : Set X)) ∉
      ChapterA.Section03.localCComponents Q) : False := by
  let N := normalizer ((blockU A).map A.subtype : Set X)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (blockU A))
  have hTN : (T : Subgroup X) ≤ N := hn.trans
    (normalizer_le_normalizer_characteristic_image A (blockU A))
  exact hbad (T.subtype hTN) (local_restrict hlocal hAN)

private theorem no_simple_model [IsSimpleGroup X] [Group.IsPerfect X]
    (T : Sylow 2 X) (hT : Nat.card T ≤ 256) (A : Subgroup X)
    (hA : IsAlternatingBlock A 5) (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hl : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (hm : ChapterA.Section02.IsTheoremCModel X) : False := by
  let := hA.2.1.elementary
  have hE : IsElementaryAbelian 2 ((blockU A).map A.subtype) := IsElementaryAbelian.map _
  cases hm with
  | alternating n hnum he => exact not_alternating_of_alternatingFive A hA hc hnum he.some
  | odd hm => exact not_oddModel_of_elementary_sixteen _ hE hc hm
  | bender hm => exact bender_no_alternating_five_block hm A hA
  | linear_binary n hnum hm => exact not_linearBinary_of_alternatingFive A hA hc T hT hnum hm
  | rank_two f hm =>
    have hr : Chapter1.Section02.LocalModels.RankTwoTheoremC X := by
      cases hm with
      | linear hf hm => exact .linear f hf hm
      | symplectic hf hm => exact .symplectic f hf hm
      | g2 hf hm => exact .g2 f hf hm
      | triality hf hm => exact .triality f hf hm
      | ree_f4 m hm _ he =>
        obtain ⟨e⟩ := he
        exact (no_alternatingFive_of_reeF4_equiv hm e A hA hc).elim
      | symplectic_derived _ he => exact .symplectic_derived he
      | g2_derived _ he => exact .g2_derived he
      | tits _ he => exact .tits he
    obtain ⟨N,_,hAN,hInv,hbad⟩ := rank_two_invariant_obstruction hr A hA hc
    exact no_invariant_escape T A N hl hn hAN hInv hbad
  | sporadic hm =>
    rcases sporadic_remaining_models A hA hE hc T hT hm with ⟨he⟩ | ⟨he⟩ | ⟨he⟩
    · let e := he.some
      let B := A.map e.toMonoidHom
      have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap A) hA
      have hBc : Nat.card ((blockU B).map B.subtype) = 16 := by
        rw [blockU_image_of_injective_restriction A e.toMonoidHom (e.injective.comp A.subtype_injective),card_map_of_injective e.injective]
        exact hc
      obtain ⟨hN,_,hbad⟩ := m22_normalizer_obstruction B hB hBc
      obtain ⟨_,hbad'⟩ := normalizer_obstruction_of_equiv e A hN hbad
      exact no_normalizer_escape T A hl hn hbad'
    · let e := he.some
      let B := A.map e.toMonoidHom
      have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap A) hA
      have hBc : Nat.card ((blockU B).map B.subtype) = 16 := by
        rw [blockU_image_of_injective_restriction A e.toMonoidHom (e.injective.comp A.subtype_injective),card_map_of_injective e.injective]
        exact hc
      obtain ⟨hN,_,hbad⟩ := m23_normalizer_obstruction B hB hBc
      obtain ⟨_,hbad'⟩ := normalizer_obstruction_of_equiv e A hN hbad
      exact no_normalizer_escape T A hl hn hbad'
    · exact no_alternatingFive_of_j2_equiv he.some A hA hc

/-- The actual full-Sylow deleted-five configuration in a quasisimple SQTK group is impossible. -/
theorem no_quasisimple_full_sylow (hsq : IsSQTK KnownSimple.IsKnownSimple X)
    [IsQuasisimple X] (T : Sylow 2 X) (hT : Nat.card T ≤ 256) (A : Subgroup X)
    (hA : IsAlternatingBlock A 5) (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hl : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (hz : Disjoint A (center X)) : False := by
  let q := QuotientGroup.mk' (center X)
  have hq := QuotientGroup.mk'_surjective (center X)
  have hqi : Function.Injective (q.comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    exact mem_bot.mpr (Subtype.ext (disjoint_def.mp hz a.property ((QuotientGroup.eq_one_iff _).mp ha)))
  let B := A.map q
  let e : A ≃* B := (MonoidHom.ofInjective hqi).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp,range_subtype]))
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv e hA
  have hBc : Nat.card ((blockU B).map B.subtype) = 16 := by
    rw [card_map_of_injective B.subtype_injective,←RankOne.Solvable.blockU_map_equiv e,card_map_of_injective e.injective]
    simpa only [card_map_of_injective A.subtype_injective] using hc
  let : Group.IsSolvable q.ker := by
    rw [show q=QuotientGroup.mk' (center X) from rfl,QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let P := T.mapSurjective hq
  have hP : Nat.card P ≤ 256 := (Nat.card_le_card_of_surjective
    (f := q.subgroupMap (T : Subgroup X)) (q.subgroupMap_surjective _)).trans hT
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Group.IsPerfect (X ⧸ center X) := Group.IsPerfect.ofSurjective hq
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model hsq
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  exact no_simple_model P hP B hB hBc
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono hn).trans (le_normalizer_map q)) hm

/-- Restrict the original Sylow and block to the actual ordinary component. -/
theorem no_containing_component_full_sylow
    (hsq : IsSQTK KnownSimple.IsKnownSimple X)
    (T : Sylow 2 X) (hT : Nat.card T ≤ 256) (A : Subgroup X)
    (hA : IsAlternatingBlock A 5) (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hl : A ∈ ChapterA.Section03.localCComponents T)
    (hn : (T : Subgroup X) ≤ normalizer (A : Set X))
    (K : Subgroup X) (hK : IsComponent X K) (hAK : A ≤ K)
    (hz : Disjoint (A.subgroupOf K) (center K)) : False := by
  let : IsQuasisimple K := hK.2
  obtain ⟨P,hP,hAP⟩ := exists_local_sylow_restriction T hl hAK hK.1
  have hPc : Nat.card P ≤ 256 := by
    have he : Nat.card P = Nat.card ((P : Subgroup K).map K.subtype) :=
      (card_map_of_injective K.subtype_injective).symm
    rw [he,hP,subgroupOf_map_subtype]
    exact (Nat.card_le_card_of_injective (inclusion (show (T : Subgroup X) ⊓ K ≤ (T : Subgroup X) from inf_le_left)) (inclusion_injective _)).trans hT
  let e := subgroupOfEquivOfLe hAK
  have hB : IsAlternatingBlock (A.subgroupOf K) 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hA
  have hBc : Nat.card ((blockU (A.subgroupOf K)).map (A.subgroupOf K).subtype) = 16 := by
    rw [card_map_of_injective (A.subgroupOf K).subtype_injective]
    rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,RankOne.Solvable.blockU_map_equiv e]
    simpa only [card_map_of_injective A.subtype_injective] using hc
  have hnP : (P : Subgroup K) ≤ normalizer (A.subgroupOf K : Set K) := by
    rw [hP,←subgroupOf_normalizer_eq hAK]
    exact comap_mono hn
  exact no_quasisimple_full_sylow (hsq.subgroup K) P hPc (A.subgroupOf K) hB hBc hAP hnP hz

end CFSG.Quasithin.Chapter2.AlternatingTerminal
