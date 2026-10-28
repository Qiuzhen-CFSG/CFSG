module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Centralizers

/-!
# The original point core in the HS branch

The natural point residual has order 768, while L and the selected component
K have orders 10752 and 3840. Their intersection therefore equals the
literal L₁. Both P and U lie there, and their relative normality and order
identify their product with O₂(L₁).

Source: Aschbacher--Smith, 14.3.33(2), printed p.1004.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem actor_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    Nat.card L = 10752 := by
  let := h.chosen.elementary
  have hc : Nat.card (pCore 2 L) = 64 := by
    rw [← card_map_of_injective L.subtype_injective]
    change Nat.card (L.pCoreIn 2) = 64
    rw [← centerSpan_eq_core h structural alternatives F s hne]
    exact (centerSpan_square_kernel_and_card h structural alternatives F s hne).2
  have hq : Nat.card (L ⧸ pCore 2 L) = 168 :=
    (Nat.card_congr (h.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).toEquiv).trans Matrix.PSL3Two.card_SL
  have ht := (pCore 2 L).card_mul_index
  rw [hc, index_eq_card, hq] at ht
  omega

theorem component_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    Nat.card K = 3840 := by
  obtain ⟨f, hf, hfk⟩ := (component_residual F s K hKH hK hKT).2.2
  have hcardCore : Nat.card (pCore 2 K) = 64 := by
    rw [← card_map_of_injective K.subtype_injective]
    change Nat.card (K.pCoreIn 2) = 64
    rw [← component_core_eq_closure h structural alternatives F s hne K hKH hK hKT hU]
    exact s.core_shape.card
  have hc := f.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, hfk, hcardCore] at hc
  have ha : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num
  rw [ha] at hc
  omega

/-- The original point residual is the literal intersection L∩K. -/
theorem point_residual_eq_inter_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U)
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hKT : F.H = K ⊔ (T : Subgroup G)) (hU : F.U = ⁅K.pCoreIn 2, K⁆) :
    F.Li L 1 = L ⊓ K := by
  apply eq_of_le_of_card_ge
    (le_inf ((F.Li_le L 1).trans inf_le_left) (point_residual_le_component F s K hKH hK hKT))
  have hd := Nat.dvd_gcd (card_dvd_of_le (show L ⊓ K ≤ L from inf_le_left))
    (card_dvd_of_le (show L ⊓ K ≤ K from inf_le_right))
  rw [actor_card h structural alternatives F s hne,
    component_card h structural alternatives F s hne K hKH hK hKT hU] at hd
  rw [point_residual_card h structural alternatives F s hne]
  exact Nat.le_of_dvd (by decide : 0 < 768) (by simpa using hd)

/-- Both factors P and U lie in the original point residual. -/
theorem core_closure_le_point_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    L.pCoreIn 2 ⊔ F.U ≤ F.Li L 1 := by
  obtain ⟨K, hKH, hK, hKT, hU, _⟩ := s.component
  rw [point_residual_eq_inter_component h structural alternatives F s hne K hKH hK hKT hU]
  exact le_inf ((core_closure_le_point_normalizer h structural alternatives F s hne).trans inf_le_left)
    (core_closure_le_component h structural alternatives F s hne K hKH hK hKT hU)

omit [Finite G] in
/-- PU is normalized by L₁ using the original relative normality of U in H. -/
theorem point_residual_normalizes_core_closure
    (F : InvariantFlag T V 3) :
    F.Li L 1 ≤ normalizer ((L.pCoreIn 2 ⊔ F.U : Subgroup G) : Set G) := by
  have hp := ((F.Li_le L 1).trans inf_le_left).trans
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hu := ((F.Li_le L 1).trans inf_le_right).trans (le_normalizer_conjugateSpanBy V F.H)
  exact (le_inf hp hu).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The literal source equality O₂(L₁)=PU. -/
theorem point_residual_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (s : LocalStructure L F) (hne : ¬ IsMulCommutative F.U) :
    (F.Li L 1).pCoreIn 2 = L.pCoreIn 2 ⊔ F.U := by
  have hle := core_closure_le_point_residual h structural alternatives F s hne
  have htwo : IsPGroup 2 (L.pCoreIn 2 ⊔ F.U : Subgroup G) :=
    IsPGroup.of_card (n := 8) (core_closure_card h structural alternatives F s hne)
  have hcore := le_pCoreIn_of_normalizes htwo hle (point_residual_normalizes_core_closure F)
  let A := (L.pCoreIn 2 ⊔ F.U).subgroupOf (F.Li L 1)
  have hAc : Nat.card A = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans
      (core_closure_card h structural alternatives F s hne)
  have hi : A.index = 3 := by
    have hc := A.card_mul_index
    rw [hAc, point_residual_card h structural alternatives F s hne] at hc
    omega
  let S : Sylow 2 (F.Li L 1) := (show IsPGroup 2 A from htwo.comap_subtype).toSylow (by rw [hi]; decide)
  exact le_antisymm (by
    have hs := pCoreIn_le_sylow (F.Li L 1) S
    change (F.Li L 1).pCoreIn 2 ≤ A.map (F.Li L 1).subtype at hs
    rwa [map_subgroupOf_eq_of_le hle] at hs) hcore

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup
