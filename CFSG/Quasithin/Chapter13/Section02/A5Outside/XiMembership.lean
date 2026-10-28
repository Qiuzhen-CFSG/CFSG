module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelComplete
public import CFSG.Quasithin.Chapter1.Section03.Basic.MinimalParabolic
public import Theory.GroupTheory.WreathTwoResidual

/-!
# Xi membership of the original outside wreath residual

The actual quotient H/O₂(H) identifies the residual quotient with E₉.
The preceding kernel theorem identifies the core of the minimal parabolic
with O₂(H). The general minimal-parabolic criterion then proves irreducibility
of the original Sylow action on both characteristic quotients. Faithful
embedding transports the result to the literal ambient subgroup O²(H).

The earlier Baumann bound and solvability remain the inputs of 13.2.9.
No extra irreducibility or quotient-action premise is used.

Source: Aschbacher–Smith, Lemma 13.2.10, printed p.881.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The original two-residual modulo its own two-core is the elementary nine-group. -/
theorem source_wreath_residual_core_quotient_model (H : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨e9⟩ := WreathTwoResidual.residual_equiv_elementaryNine
  let r := (((pResidual 2 (H ⧸ pCore 2 H)).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))).trans e9
  have hc : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 9 := by
    rw [Nat.card_congr r.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hz : pCore 2 (pResidual 2 (H ⧸ pCore 2 H)) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases (pCore_isPGroup (p := 2) (G := pResidual 2 (H ⧸ pCore 2 H))).card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans (pCore 2 (pResidual 2 (H ⧸ pCore 2 H))).card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd
  exact ⟨(q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective _) hk).trans
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans r)⟩

/-- Original 13.2.10, unstarred Xi membership of the literal embedded residual. -/
theorem source_wreath_residual_mem_Xi
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) :
    (pResidual 2 H).map H.subtype ∈ Chapter1.Xi G (T : Subgroup G) := by
  let S := T.subtype hH.1.1.2
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hcore : ChapterB.minimalParabolicCore S h.2.2.1 = pCore 2 H :=
    (source_core_eq_omega_centralizer d hH hB hZ hs).trans
      (source_omega_centralizer_eq_twoCore d hH hB hZ hs)
  let : IsElementaryAbelian 3 (Chapter1.XiQuotient (pResidual 2 H)) :=
    source_residual_core_quotient_elementary d hH hB hZ hs
  obtain ⟨f⟩ := source_wreath_residual_core_quotient_model H e
  have hc : Nat.card (Chapter1.XiQuotient (pResidual 2 H)) = 3^2 := by
    rw [Nat.card_congr f.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have htop : (⊤ : Subgroup H) ∈ Chapter1.H H := by
    intro hb
    apply hH.1.1.1
    have hm := congrArg (Subgroup.map H.subtype) hb
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective] at hm
    simpa only [←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hm
  have hXi := Chapter1.residual_mem_Xi_of_minimalParabolic_core_eq S h.2.2.1 hcore
    htop (by decide : Nat.Prime 3) (by decide : Odd 3) hc
  have hx := (Chapter1.mem_Xi_map_iff H.subtype H.subtype_injective).mpr hXi
  change (pResidual 2 H).map H.subtype ∈ Chapter1.Xi G
    (((T : Subgroup G).subgroupOf H).map H.subtype) at hx
  rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hx

end CFSG.Quasithin.Chapter13.Section02.A5Outside
