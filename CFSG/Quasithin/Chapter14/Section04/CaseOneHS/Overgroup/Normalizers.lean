module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.PointCore

/-!
# The original HS normalizers before excluding the outer shadow

The common Sylow subgroup PU identifies the indices in H of K and L₁.
Consequently L₁T has prime index five in H. Escape excludes the only larger
point intersection. The full natural L-action then factors N_G(V) through
L and that intersection, giving N_G(V)=N_G(L)=LT on the original subgroups.

Source: Aschbacher--Smith, 14.3.7 and 14.3.33, printed pp.992,1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original Sylow subgroup normalizes the literal point residual. -/
theorem sylow_normalizes_point_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
  have hi : (T : Subgroup G) ≤ normalizer (L ⊓ F.H : Set G) :=
    (le_inf (h.sylow_normalizes_at structural) ((F.invariant 1).trans F.H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  change (T : Subgroup G) ≤ normalizer
    ((pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype : Set G)
  exact hi.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (L ⊓ F.H : Subgroup G)))

/-- The source core product is contained in the original ambient Sylow. -/
theorem core_closure_le_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) :
    L.pCoreIn 2 ⊔ F.U ≤ (T : Subgroup G) := by
  let := h.chosen.elementary
  apply sup_le ?_ (closure_le_sylow F s)
  exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer (h.sylow_normalizes_at structural))).trans
      (by simpa using pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right))

/-- The point residual together with T has index five in H. -/
theorem point_join_sylow_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf F.H).index = 5 := by
  obtain ⟨K, hKH, hK, hKT, hU, _⟩ := s.component
  obtain ⟨S, hS⟩ := core_closure_sylow h structural alternatives F s hne K hKH hK hKT hU
  have hTK : (T : Subgroup G) ⊓ K = L.pCoreIn 2 ⊔ F.U := by
    rw [← hS]
    exact inf_eq_sylow_map S T.isPGroup' (hS ▸ core_closure_le_sylow h structural F s)
  have hTL : (T : Subgroup G) ⊓ F.Li L 1 = L.pCoreIn 2 ⊔ F.U := by
    apply le_antisymm
    · exact (inf_le_inf_left _ (point_residual_le_component F s K hKH hK hKT)).trans hTK.le
    · exact le_inf (core_closure_le_sylow h structural F s)
        (core_closure_le_point_residual h structural alternatives F s hne)
  have hnormal := (component_residual F s K hKH hK hKT).1
  have hnK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hnormal)
  have hcH := card_mul_eq_card_inf_mul_card_sup_of_normalizes K (T : Subgroup G) hnK
  rw [← hKT, inf_comm K, hTK, core_closure_card h structural alternatives F s hne,
    component_card h structural alternatives F s hne K hKH hK hKT hU] at hcH
  have hcJ := card_mul_eq_card_inf_mul_card_sup_of_normalizes (F.Li L 1) (T : Subgroup G)
    (sylow_normalizes_point_residual h structural F)
  rw [inf_comm (F.Li L 1), hTL, core_closure_card h structural alternatives F s hne,
    point_residual_card h structural alternatives F s hne] at hcJ
  have hJH : F.Li L 1 ⊔ (T : Subgroup G) ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  let A := (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf F.H
  have he := Nat.card_congr (subgroupOfEquivOfLe hJH).toEquiv
  have hi := A.card_mul_index
  change Nat.card A = _ at he
  have hpos := Nat.card_pos (α := A)
  rw [← he] at hcJ
  change A.index = 5
  nlinarith

/-- The original point intersection is exactly L₁T. -/
theorem seed_normalizer_inter_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    normalizer (V : Set G) ⊓ F.H = F.Li L 1 ⊔ (T : Subgroup G) := by
  have hJH : F.Li L 1 ⊔ (T : Subgroup G) ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hJN : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
    sup_le (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
      (F.last ▸ F.invariant 3)
  let A := (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf F.H
  let B := (normalizer (V : Set G) ⊓ F.H).subgroupOf F.H
  have hAB : A ≤ B := by intro x hx; exact ⟨hJN hx, x.property⟩
  have hi : A.index = 5 := point_join_sylow_index h structural alternatives F s hne
  have hmax : IsCoatom A := by
    refine ⟨fun ht => by simp [ht] at hi, fun C hAC => ?_⟩
    have hm := relIndex_mul_index hAC.le
    rw [hi] at hm
    have hp : (A.relIndex C * C.index).Prime := hm ▸ (by decide : Nat.Prime 5)
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hC⟩ | ⟨_, hrel⟩
    · exact index_eq_one.mp hC
    · exact (hAC.not_ge (relIndex_eq_one.mp hrel)).elim
  have hB : B ≠ ⊤ := by
    intro he
    apply h.flag_escape_at F alternatives
    intro x hx
    have hm : (⟨x, hx⟩ : F.H) ∈ B := he ▸ mem_top _
    exact h.seed_normalizer_le_at structural hm.1
  have he : A = B := (eq_or_lt_of_le hAB).resolve_right (fun hlt => hB (hmax.2 B hlt))
  have hm := congrArg (map F.H.subtype) he
  rw [map_subgroupOf_eq_of_le hJH, map_subgroupOf_eq_of_le inf_le_right] at hm
  exact hm.symm

/-- Original 14.3.33: before the outer shadow is excluded, M=LT. -/
theorem seed_normalizer_eq_actor_join_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    normalizer (V : Set G) = L ⊔ (T : Subgroup G) := by
  apply le_antisymm ?_ (sup_le h.chosen.normalizes (F.last ▸ F.invariant 3))
  intro x hx
  obtain ⟨l, hl, he⟩ := h.full_L_action (V.normalizerMonoidHom ⟨x, hx⟩)
  have hc : l⁻¹ * x ∈ centralizer (V : Set G) := by
    intro v hv
    have he' := he ⟨v, hv⟩
    change l * v * l⁻¹ = x * v * x⁻¹ at he'
    have hh := congrArg (fun a : G => l⁻¹ * a * x) he'
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  have hmem : l⁻¹ * x ∈ normalizer (V : Set G) ⊓ F.H :=
    ⟨(normalizer _).mul_mem ((normalizer _).inv_mem (h.chosen.normalizes hl)) hx,
      ((centralizer_le (F.le_seed 1)).trans (Subgroup.centralizer_le_normalizer _)) hc⟩
  rw [seed_normalizer_inter_point h structural alternatives F s hne] at hmem
  have hle : F.Li L 1 ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup_right ((F.Li_le L 1).trans inf_le_left) _
  have hh := (L ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hl) (hle hmem)
  simpa only [mul_inv_cancel_left] using hh

/-- The two full ambient normalizers both equal the original LT. -/
theorem actor_normalizer_eq_actor_join_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) :=
  (actor_normalizer_eq_seed_normalizer h structural alternatives F s hne).trans
    (seed_normalizer_eq_actor_join_sylow h structural alternatives F s hne)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
