module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.CubicCentralizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.SourceReduction

/-!
# The original overgroups in the order-eight shadow

Coprime decomposition of the original seed shows that C_Q(X₁) fixes V,
so lies in O₂(LT). Its intersection with L is exactly Z(U). In the
order-eight branch the actual Sylow has order 1024, and the subgroup
orders identify LT=LC_Q(X₁). The original action kernel then gives
O₂(LT)=PC_Q(X₁). These retain the source actors and embeddings for the
subsequent construction of the outer involution and its fusion analysis;
they do not exclude the shadow by group orders alone.

Source: Aschbacher--Smith, proof of 14.3.33(3), printed p.1005.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The cubic centralizer fixes the original seed, hence lies in O₂(LT).
Coprime decomposition of V uses its actual fixed point V₁. -/
theorem core_cubic_centralizer_le_actor_join_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := h.chosen.elementary
  let C := F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)
  have hXH := (F.Li_le L 1 hx).2
  let := F.localKernel_tilde_seed_elementary
  have hVX : V ⊓ centralizer (zpowers x : Set G) = F.Vi 1 := by
    have hVU : V ≤ F.U := le_conjugateSpanBy V F.H
    calc
      V ⊓ centralizer (zpowers x : Set G) = V ⊓ (F.U ⊓ centralizer (zpowers x : Set G)) := by
        rw [← inf_assoc,inf_eq_left.mpr hVU]
      _ = V ⊓ F.ZU := congrArg (V ⊓ ·) (closure_cubic_centralizer F s x hXH hx3)
      _ = F.Vi 1 := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking (by decide) hne
  have hn : zpowers x ≤ normalizer (V : Set G) :=
    (zpowers_le.mpr (F.Li_le L 1 hx).1).trans h.chosen.normalizes
  have hcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hcop : Nat.Coprime (Nat.card (zpowers x)) (Nat.card V) := by
    rw [Nat.card_zpowers,hx3,hcard]
    decide
  have hVdec : V = ⁅V,zpowers x⁆ ⊔ F.Vi 1 :=
    (eq_commutator_sup_centralizer_of_solvable_coprime V (zpowers x) hn inferInstance hcop).trans
      (congrArg (⁅V,zpowers x⁆ ⊔ ·) hVX)
  have hCD := core_cubic_centralizes_commutator F s x hXH hx3
  have hCH : C ≤ F.H := inf_le_left.trans (pCoreIn_le 2 F.H)
  obtain ⟨z,_,hz,hH⟩ := source_point_centralizer F
  have hCpoint : C ≤ centralizer (F.Vi 1 : Set G) := by
    rw [hz,zpowers_eq_closure,centralizer_closure,← hH]
    exact hCH
  have hCV : C ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mp
    rw [hVdec]
    exact sup_le (le_centralizer_iff.mp (hCD.trans
      (centralizer_le (commutator_mono (le_conjugateSpanBy V F.H) le_rfl))))
      (le_centralizer_iff.mp hCpoint)
  rw [← h.centralizer_LT_at structural]
  exact le_inf ((inf_le_left.trans (point_core_le_sylow F)).trans le_sup_right) hCV

/-- The order-eight alternative has the source Sylow order 2¹⁰. -/
theorem sylow_card_of_point_core_card
    (F : InvariantFlag T V 3) (s : LocalStructure L F)
    (hc : Nat.card (F.H.pCoreIn 2) = 128) : Nat.card T = 1024 := by
  have hcore : Nat.card (pCore 2 F.H) = 128 := by
    rw [← card_map_of_injective F.H.subtype_injective]
    exact hc
  obtain ⟨e⟩ := s.quotient F
  have hquot : Nat.card (F.H ⧸ pCore 2 F.H) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hcard : Nat.card F.H = 15360 := by
    have hh := (pCore 2 F.H).card_mul_index
    rw [hcore,index_eq_card,hquot] at hh
    omega
  have hS := (T.subtype (show (T : Subgroup G) ≤ F.H from F.invariant 1)).card_eq_multiplicity
  have he := Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ F.H from F.invariant 1)).toEquiv
  rw [hcard] at hS
  change Nat.card ((T : Subgroup G).subgroupOf F.H) = _ at hS
  rw [he] at hS
  exact hS.trans (by decide +kernel)

/-- The actual cubic centralizer meets L precisely in the cyclic center. -/
theorem core_cubic_centralizer_inter_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3) :
    L ⊓ (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) = F.ZU := by
  let := h.chosen.elementary
  obtain ⟨K,hKH,hK,hKT,hU,_⟩ := s.component
  have hUC := (point_core_cubic_supplement h structural alternatives F s hne x hx hx3).2
  have hUL := closure_le_actor h structural alternatives F s hne
  apply le_antisymm ?_ (hUC.symm.le.trans (inf_le_inf hUL le_rfl))
  rintro a ⟨haL,haC⟩
  have haM := core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3 haC
  have haV := h.chosen.core_centralizes haM
  have haP : a ∈ L.pCoreIn 2 := h.centralizer_L ▸ ⟨haL,haV⟩
  have haK := core_closure_le_component h structural alternatives F s hne K hKH hK hKT hU
    (mem_sup_left haP)
  have haU : a ∈ F.U := (component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU).symm ▸
    (inf_pCoreIn_le_of_le 2 hKH ⟨haK,haC.1⟩)
  exact hUC ▸ ⟨haU,haC⟩

/-- In the surviving outer alternative, M=LT is the original product LC_Q(X₁). -/
theorem actor_join_sylow_eq_join_cubic_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hc : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    L ⊔ (T : Subgroup G) = L ⊔ (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) := by
  let := h.chosen.elementary
  have hCT : F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) ≤ (T : Subgroup G) :=
    inf_le_left.trans (point_core_le_sylow F)
  have hQcard : Nat.card (F.H.pCoreIn 2) = 128 := by
    rw [point_core_card_eq_sixteen_mul_cubic_centralizer h structural alternatives F s hne x hx hx3,hc]
  have hT := sylow_card_of_point_core_card F s hQcard
  have hi := sylow_inter_actor_card h structural alternatives F s hne
  rw [inf_comm] at hi
  have hL := actor_card h structural alternatives F s hne
  have hM := card_mul_eq_card_inf_mul_card_sup_of_normalizes L (T : Subgroup G)
    (h.sylow_normalizes_at structural)
  rw [hT,hL,hi] at hM
  have hLC := card_mul_eq_card_inf_mul_card_sup_of_normalizes L
    (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) (hCT.trans (h.sylow_normalizes_at structural))
  obtain ⟨e⟩ := center_model F s
  have hZ : Nat.card F.ZU = 4 := (Nat.card_congr e.toEquiv).trans (Nat.card_zmod 4)
  rw [hL,hc,core_cubic_centralizer_inter_actor h structural alternatives F s hne x hx hx3,hZ] at hLC
  exact (eq_of_le_of_card_ge (sup_le_sup_left hCT L) (by omega)).symm

/-- The actual outer core is PC_Q(X₁), retaining the original action kernel. -/
theorem actor_join_core_eq_join_cubic_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (x : G) (hx : x ∈ F.Li L 1) (hx3 : orderOf x = 3)
    (hc : Nat.card (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G) : Subgroup G) = 8) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      L.pCoreIn 2 ⊔ (F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)) := by
  let := h.chosen.elementary
  let C := F.H.pCoreIn 2 ⊓ centralizer (zpowers x : Set G)
  have hCM := core_cubic_centralizer_le_actor_join_core h structural F s hne x hx hx3
  have hPM : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [← centerSpan_eq_core h structural alternatives F s hne]
    exact centerSpan_le_core h structural F s
  apply le_antisymm ?_ (sup_le hPM hCM)
  intro a ha
  have haM := pCoreIn_le 2 (L ⊔ (T : Subgroup G)) ha
  rw [actor_join_sylow_eq_join_cubic_centralizer h structural alternatives F s hne x hx hx3 hc] at haM
  have hn : C ≤ normalizer (L : Set G) :=
    (inf_le_left.trans (point_core_le_sylow F)).trans (h.sylow_normalizes_at structural)
  have hprod : a ∈ (L : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L C hn]
    exact haM
  obtain ⟨l,hl,c,hcC,rfl⟩ := hprod
  have hcV := h.chosen.core_centralizes (hCM hcC)
  have hlV : l ∈ centralizer (V : Set G) := by
    have hh := (centralizer (V : Set G)).mul_mem (h.chosen.core_centralizes ha)
      ((centralizer _).inv_mem hcV)
    simpa only [mul_inv_cancel_right] using hh
  exact mul_mem_sup (h.centralizer_L ▸ ⟨hl,hlV⟩) hcC

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
