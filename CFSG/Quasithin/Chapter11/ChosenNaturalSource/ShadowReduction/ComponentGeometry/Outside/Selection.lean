module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Products
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan

/-!
# Residual-compatible selection inside the point centralizer

The proved product forces K or its quotient centralizer outside M.
Adjoin the original Sylow and descend to an H-star subgroup. Its two-residual
lies in the chosen normal factor because the quotient by that factor is a
two-group. This constructs the source alternative with O²(H) in both clauses.
Generation one and the smaller R₁-Sylow witness are separate obligations.

Source: Aschbacher--Smith, selection on printed p.779 following 11.5.1.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Minimal descent inside any escaping overgroup of T in the point centralizer. -/
theorem exists_HStar_below_point (h : Comparison.EarlierGeometry E)
    (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J) (hJz : J ≤ Gz E) (hout : ¬ J ≤ E.M) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ J := by
  classical
  have ho := (point_involution E h.point_mem h.point_fixed h.point_ne_one).1
  have hp : IsPGroup 2 (zpowers E.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
  have hP : zpowers E.z ≤ J :=
    (zpowers_le.mpr (D.le_sylow (E.V₁_le h.point_mem))).trans hTJ
  have hn : J ≤ normalizer (zpowers E.z : Set G) := by
    rw [point_normalizer_eq E h.point_mem h.point_fixed h.point_ne_one]
    exact hJz
  have hJ : J ∈ Chapter1.H G := by
    intro he
    have hz := le_pCoreIn_of_normalizes hp hP hn (mem_zpowers E.z)
    exact h.point_ne_one (mem_bot.mp (he ▸ hz))
  let family : Set (Subgroup G) :=
    {H | (H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ E.M) ∧ H ≤ J}
  have hmem : J ∈ family := ⟨⟨⟨hJ,hTJ⟩,hout⟩,le_rfl⟩
  obtain ⟨H,hH⟩ := (Set.toFinite family).exists_minimalFor id family ⟨J,hmem⟩
  exact ⟨H, ⟨hH.1.1, fun B hB hBH => hH.2 ⟨hB,hBH.trans hH.1.2⟩ hBH⟩,hH.1.2⟩

omit [Finite G] in
/-- The two-residual of a subgroup of WT lies in the T-normalized factor W. -/
theorem residual_le_factor (W H : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hH : H ≤ W ⊔ (T : Subgroup G)) : (pResidual 2 H).map H.subtype ≤ W := by
  let J := W ⊔ (T : Subgroup G)
  let N := W.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le W.le_normalizer hn)
  have hq := isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf J)
    T.isPGroup'.comap_subtype (codisjoint_subgroupOf_sup W (T : Subgroup G)).eq_top
  let f := (QuotientGroup.mk' N).comp (inclusion hH)
  have hr := pResidual_le_ker_of_isPGroup 2 f hq
  rintro _ ⟨x,hx,rfl⟩
  exact (QuotientGroup.eq_one_iff (N := N) (inclusion hH x)).mp (hr hx)

private theorem select_in_normal_factor (h : Comparison.EarlierGeometry E)
    (W : Subgroup G) (hWz : W ≤ Gz E) (hn : Gz E ≤ normalizer (W : Set G))
    (hout : ¬ W ≤ E.M) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ Gz E ∧
      (pResidual 2 H).map H.subtype ≤ W := by
  have hJz : W ⊔ (T : Subgroup G) ≤ Gz E := sup_le hWz h.sylow_le_pointCentralizer
  obtain ⟨H,hH,hHJ⟩ := exists_HStar_below_point E h _ le_sup_right hJz
    (fun hJ => hout (le_sup_left.trans hJ))
  exact ⟨H,hH,hHJ.trans hJz,
    residual_le_factor W H (h.sylow_le_pointCentralizer.trans hn) hHJ⟩

/-- Existential source selection, without supplying H or its residual
alternative as an input. The model outer-group premise is still explicit. -/
theorem exists_selected_H (h : Comparison.EarlierGeometry E) (he : E.Kz = E.K)
    (hNT : normalizer (T : Set G) ≤ E.M)
    (ho : ChapterE.IsTwoClosed (MulAut.Outer (E.K ⧸ pCore 2 E.K)))
    (h1132 : ∀ H, Hypothesis1131At D E.input E.point H →
      Proposition1132At D E.input E.point H) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ Gz E ∧
      SelectedResidualAlternative { E with H := H } := by
  obtain ⟨J,hJ,hJz⟩ := exists_outside_in_pointCentralizer E
    h.point_mem h.point_fixed h.point_ne_one h1132
  have hescape : ¬ Gz E ≤ E.M := fun hg => hJ.1.2 (hJz.trans hg)
  have hcases : ¬ E.K ≤ E.M ∨ ¬ Yz E ≤ E.M := by
    by_cases hK : E.K ≤ E.M
    · right
      intro hY
      apply hescape
      calc
        Gz E = E.K ⊔ Yz E ⊔ Mz E := point_decomposition E h he hNT ho
        _ ≤ E.M := sup_le (sup_le hK hY) inf_le_left
    · exact Or.inl hK
  rcases hcases with hK | hY
  · obtain ⟨H,hH,hHz,hr⟩ := select_in_normal_factor E h E.K
      (he ▸ h.point_component.1) (point_normalizes_component E he) hK
    exact ⟨H,hH,hHz,Or.inr hr⟩
  · obtain ⟨H,hH,hHz,hr⟩ := select_in_normal_factor E h (Yz E) inf_le_left
      (point_normalizes_kernel E he) hY
    refine ⟨H,hH,hHz,Or.inl ?_⟩
    change ⁅E.K, (pResidual 2 H).map H.subtype⁆ ≤ E.K.pCoreIn 2
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx k hk
    exact Closure.coreQuotientCentralizer_commutator (hr hx).2 hk

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
