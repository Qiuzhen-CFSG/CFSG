module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CoreCentralizer
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Reduction of the HS overgroup conclusion to its point core

If U=O₂(H), the original S₅ quotient gives |T|=512. Relative normality
of L in LT identifies T∩L as a Sylow subgroup of L, also of order 512.
Thus T lies in L, and the already proved N_G(V)=LT becomes N_G(V)=L.
The conditional HS consumer uses this implication; the source transfer
argument must still establish U=O₂(H).

Source: Aschbacher--Smith, 14.3.33(3) and the following I.4.8 application,
printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- If the original point core equals U, the ambient Sylow has order 512. -/
theorem sylow_card_of_closure_core
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hU : F.U = F.H.pCoreIn 2) :
    Nat.card T = 512 := by
  have hcore : Nat.card (pCore 2 F.H) = 64 := by
    rw [← card_map_of_injective F.H.subtype_injective]
    change Nat.card (F.H.pCoreIn 2) = 64
    rw [← hU]
    exact s.core_shape.card
  obtain ⟨e⟩ := s.quotient F
  have hquot : Nat.card (F.H ⧸ pCore 2 F.H) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hcard : Nat.card F.H = 7680 := by
    have hc := (pCore 2 F.H).card_mul_index
    rw [hcore, index_eq_card, hquot] at hc
    omega
  have hS := (T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)).card_eq_multiplicity
  have he := Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ F.H from F.invariant 1)).toEquiv
  rw [hcard] at hS
  change Nat.card ((T : Subgroup G).subgroupOf F.H) = _ at hS
  rw [he] at hS
  exact hS.trans (by decide +kernel)

/-- The original T∩L has order 512, using relative normality in LT. -/
theorem sylow_inter_actor_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nat.card ((T : Subgroup G) ⊓ L : Subgroup G) = 512 := by
  let J := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer (show L ≤ J from le_sup_left)).mpr
    (sup_le L.le_normalizer (h.sylow_normalizes_at structural))
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  obtain ⟨R, hR⟩ := S.exists_sylow_map_eq_inf_of_normal N
  have hNc : Nat.card N = 10752 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).toEquiv).trans
      (actor_card h structural alternatives F s hne)
  have hc := R.card_eq_multiplicity
  rw [hNc] at hc
  have hm := congrArg (map J.subtype) hR
  rw [map_inf _ _ _ J.subtype_injective,
    map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)] at hm
  change ((R : Subgroup N).map N.subtype).map J.subtype =
    ((T : Subgroup G).subgroupOf J).map J.subtype ⊓ L at hm
  rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hm
  rw [← hm, card_map_of_injective J.subtype_injective,
    card_map_of_injective N.subtype_injective]
  exact hc.trans (by decide +kernel)

/-- Once Q=U, the actual ambient Sylow lies in L. -/
theorem sylow_le_actor_of_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (hU : F.U = F.H.pCoreIn 2) : (T : Subgroup G) ≤ L := by
  have he : (T : Subgroup G) ⊓ L = (T : Subgroup G) := eq_of_le_of_card_ge inf_le_left (by
    rw [sylow_inter_actor_card h structural alternatives F s hne, sylow_card_of_closure_core F s hU])
  exact inf_eq_left.mp he

/-- The seed normalizer is L after the sole remaining point-core equality.
The order-eight shadow exclusion must still supply that equality. -/
theorem seed_normalizer_eq_actor_of_closure_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (hU : F.U = F.H.pCoreIn 2) : normalizer (V : Set G) = L := by
  rw [seed_normalizer_eq_actor_join_sylow h structural alternatives F s hne,
    sup_eq_left.mpr (sylow_le_actor_of_closure_core h structural alternatives F s hne hU)]

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
