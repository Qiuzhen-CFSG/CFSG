module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Selection
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.ChapterE.Defs
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The residual-compatible outside H choice

The source decomposition G₁=KYM₁ forces K or Y outside M. Adjoin T to
that factor and descend to a minimal member of H(T) outside M. Its
two-residual lies in the chosen factor, since the quotient is a two-group.
Thus both source residual alternatives and centralization of V₁ survive
selection. Normality is used only inside the relevant joins.
Source: Aschbacher--Smith, selection preceding 11.5.2 and Lemma 11.5.4,
printed pp.779--780.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Both factors in the literal definition of Y are normal in G₁. -/
theorem G₁_normalizes_Y : E.G₁ ≤ normalizer (E.Y : Set G) :=
  (le_inf (normalizer_le_normalizer_centralizer E.V₁)
    (E.G₁_normalizes_K.trans (normalizer_normalizes_coreQuotientCentralizer E.K))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite G] in
private theorem residual_le_factor (W H : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (W : Set G))
    (hH : H ≤ W ⊔ (T : Subgroup G)) : (pResidual 2 H).map H.subtype ≤ W := by
  let J := W ⊔ (T : Subgroup G)
  let N := W.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le W.le_normalizer hn)
  let q := QuotientGroup.mk' N
  have hsup : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ :=
    (codisjoint_subgroupOf_sup W (T : Subgroup G)).eq_top
  have hq := isPGroup_quotient_of_sup_eq_top N ((T : Subgroup G).subgroupOf J)
    T.isPGroup'.comap_subtype hsup
  let f := q.comp (inclusion hH)
  have hk : IsPGroup 2 (H ⧸ f.ker) :=
    (hq.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hle : pResidual 2 H ≤ f.ker := sInf_le ⟨inferInstance, hk⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff (N := N) (inclusion hH x)).mp (hle hx)

private theorem exists_HStar_below (hp : E.point ≠ ⊥) (J : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ J) (hJG : J ≤ E.G₁) (hJM : ¬ J ≤ E.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ J := by
  classical
  let S : Set (Subgroup G) :=
    {H | (H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ E.M) ∧ H ≤ J}
  have hJ : J ∈ S := ⟨⟨⟨E.point_overgroup_mem_H hp J hTJ hJG, hTJ⟩, hJM⟩, le_rfl⟩
  obtain ⟨H, hH⟩ := (Set.toFinite S).exists_minimalFor id S ⟨J, hJ⟩
  refine ⟨H, ⟨hH.1.1, ?_⟩, hH.1.2⟩
  intro B hB hBH
  exact hH.2 ⟨hB, hBH.trans hH.1.2⟩ hBH

/-- The two simultaneous requirements in the source choice of H.
Here the superscript O² is represented by pResidual, never by pCore. -/
theorem exists_residual_selected_H (hp : E.point ≠ ⊥)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hc : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hKC : E.K ≤ centralizer (E.V₁ : Set G))
    (hfactor : E.G₁ ≤ E.K ⊔ E.Y ⊔ E.M₁) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ E.G₁ ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (E.V₁ : Set G) ∧
      ((pResidual 2 H).map H.subtype ≤ E.K ∨
        ⁅E.K, (pResidual 2 H).map H.subtype⁆ ≤ E.K.pCoreIn 2) := by
  have hout : ¬ E.G₁ ≤ E.M := fun h => hc ((centralizer_le_normalizer _).trans h)
  have hcases : ¬ E.K ≤ E.M ∨ ¬ E.Y ≤ E.M := by
    by_cases hK : E.K ≤ E.M
    · right
      intro hY
      exact hout (hfactor.trans (sup_le (sup_le hK hY) inf_le_left))
    · exact Or.inl hK
  rcases hcases with hK | hY
  · have hJG : E.K ⊔ (T : Subgroup G) ≤ E.G₁ := sup_le E.K_le_G₁ hT1
    obtain ⟨H, hH, hHJ⟩ := E.exists_HStar_below hp _ le_sup_right hJG
      (fun h => hK (le_sup_left.trans h))
    have hr := residual_le_factor E.K H (hT1.trans E.G₁_normalizes_K) hHJ
    exact ⟨H, hH, hHJ.trans hJG, hr.trans hKC, Or.inl hr⟩
  · have hJG : E.Y ⊔ (T : Subgroup G) ≤ E.G₁ := sup_le E.Y_le_G₁ hT1
    obtain ⟨H, hH, hHJ⟩ := E.exists_HStar_below hp _ le_sup_right hJG
      (fun h => hY (le_sup_left.trans h))
    have hr := residual_le_factor E.Y H (hT1.trans E.G₁_normalizes_Y) hHJ
    refine ⟨H, hH, hHJ.trans hJG, hr.trans inf_le_left, Or.inr ?_⟩
    rw [commutator_comm]
    apply commutator_le.mpr
    intro x hx k hk
    exact coreQuotientCentralizer_commutator (hr hx).2 hk

/-- In the K=L₁ branch the selected residual necessarily centralizes K/O₂(K). -/
theorem selected_residual_centralizes_of_equal (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hTM : (T : Subgroup G) ≤ E.M) (hKL : E.K = E.L₁)
    (hselect : (pResidual 2 H).map H.subtype ≤ E.K ∨
      ⁅E.K, (pResidual 2 H).map H.subtype⁆ ≤ E.K.pCoreIn 2) :
    ⁅E.K, (pResidual 2 H).map H.subtype⁆ ≤ E.K.pCoreIn 2 := by
  apply hselect.resolve_left
  intro hR
  have hRM : (pResidual 2 H).map H.subtype ≤ E.M := by
    rw [hKL] at hR
    exact hR.trans (E.L₁_le.trans L.le_normalizer)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at he
  exact hH.1.2 (he ▸ sup_le hRM hTM)

/-- The selected H still lies in Gz, so the preceding 11.4.4 applies
to this new choice as well as to the originally selected outside subgroup. -/
theorem exists_residual_selected_H_parameter_one (hp : E.point ≠ ⊥)
    (hT1 : (T : Subgroup G) ≤ E.G₁)
    (hc : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hKC : E.K ≤ centralizer (E.V₁ : Set G))
    (hfactor : E.G₁ ≤ E.K ⊔ E.Y ⊔ E.M₁)
    (hz : E.z ∈ E.V₁) (hTz : (T : Subgroup G) ≤ centralizer ({E.z} : Set G))
    (h1144 : ∀ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) E.M →
      H ≤ centralizer ({E.z} : Set G) → ChapterE.generationParameter H = 1) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) E.M ∧ H ≤ E.G₁ ∧
      H ≤ centralizer ({E.z} : Set G) ∧ ChapterE.generationParameter H = 1 ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (E.V₁ : Set G) ∧
      ((pResidual 2 H).map H.subtype ≤ E.K ∨
        ⁅E.K, (pResidual 2 H).map H.subtype⁆ ≤ E.K.pCoreIn 2) := by
  obtain ⟨H, hH, hHG, hR, hselect⟩ := E.exists_residual_selected_H hp hT1 hc hKC hfactor
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at he
  have hHz : H ≤ centralizer ({E.z} : Set G) := by
    rw [← he]
    exact sup_le (hR.trans (centralizer_le (Set.singleton_subset_iff.mpr hz))) hTz
  exact ⟨H, hH, hHG, hHz, h1144 H hH hHz, hR, hselect⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
