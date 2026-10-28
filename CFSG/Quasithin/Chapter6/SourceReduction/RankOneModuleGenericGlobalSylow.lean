module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry

/-!
# The common Sylow and enlarged-core identities in the generic amalgams

For the whole residual K = O²(H), the odd Cartan B lies in K and hence
in both parabolics. Since BT is the original intersection N_G(L) ∩ H,
A.1.6 puts O₂(GᵢT) in the original S. In the ordinary rows S lies in
both factors, so restriction gives O₂(GᵢT) ≤ O₂(Lᵢ); characteristic
normality gives the reverse containment. Sylow maximality identifies
S with both T ∩ Lᵢ.

The catalogue comparison supplies the containment of S in the ordinary
rows. The degree-two unitary extension requires its reduced common Sylow
and is not covered by that containment. Its enlarged core is normal in
the full overlap, however, so the diagonal-torus parity calculation puts
it in both local factors. Thus every concrete comparison now gives
O₂(GᵢT) = O₂(Lᵢ). Neither right-factor maximality
nor exhaustive comparison or ambient recognition is asserted here.
Source: Aschbacher–Smith 5.2.6–7, printed pp.650–651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The classification-free A.1.6 step in 5.2.7: adjoining T to either
actual parabolic puts its two-core in the original intersection core S.
This also applies before reducing the degree-two unitary extension. -/
theorem Preparation.parabolic_sylow_core_le_sourceS
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (d : Preparation T L H A B (residual H))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (i : Fin 2) :
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊔
      (T : Subgroup G)).pCoreIn 2 ≤ sourceS L H := by
  have hBP : B ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i := by
    fin_cases i
    · change B ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
      rw [d.parabolic_zero]
      exact (le_inf le_rfl (right_cartan_le_residual d.cartans)).trans le_sup_right
    · exact (right_cartan_le_residual d.cartans).trans (le_sup_left.trans le_sup_left)
  apply Chapter3.twoCore_le_of_sylow_le T (le_inf hTL hTH)
  change normalizer (L : Set G) ⊓ H ≤ _
  rw [← d.cartans.sylow_sup_right hTL hTH]
  exact sup_le le_sup_right (hBP.trans le_sup_left)

/-- The common Sylow and both GᵢT-core identities of 5.2.7 in its ordinary
rows. Containment of the original S is the earlier model conclusion of
5.2.6, rather than an additional equality of cores. -/
theorem Preparation.ordinary_sylow_core_geometry
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
    (hS : ∀ i : Fin 2, sourceS L H ≤ ![L,residual H] i) :
    (∀ i : Fin 2, sourceS L H = (T : Subgroup G) ⊓ ![L,residual H] i) ∧
    (∀ i : Fin 2,
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊔ (T : Subgroup G)).pCoreIn 2 =
        (![L,residual H] i).pCoreIn 2) := by
  have hST := sourceS_le_sylow h.sylow_normalizes hTH
  have hf := d.hypothesisF11 h hTH
  have hn (i : Fin 2) :
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊔ (T : Subgroup G) ≤
        normalizer (![L,residual H] i : Set G) := by
    refine sup_le ((normal_subgroupOf_iff_le_normalizer
      (show ![L,residual H] i ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i from
        le_sup_left.trans le_sup_left)).mp (hf.local_normal_in_parabolic i)) ?_
    fin_cases i
    · exact h.sylow_normalizes
    · exact hTH.trans (le_normalizer_residual H)
  constructor
  · intro i
    obtain ⟨P,hP⟩ := d.sylow i
    rw [inf_eq_left.mpr (hS i)] at hP
    have hPT : (P : Subgroup (![L,residual H] i)) ≤
        (T : Subgroup G).subgroupOf (![L,residual H] i) := by
      intro x hx
      exact hST (hP ▸ mem_map_of_mem (![L,residual H] i).subtype hx)
    have he := congrArg (Subgroup.map (![L,residual H] i).subtype)
      (P.is_maximal' T.isPGroup'.comap_subtype hPT)
    change ((T : Subgroup G).subgroupOf (![L,residual H] i)).map (![L,residual H] i).subtype =
      (P : Subgroup (![L,residual H] i)).map (![L,residual H] i).subtype at he
    rw [subgroupOf_map_subtype,hP] at he
    exact he.symm
  · intro i
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
    let Y := P ⊔ (T : Subgroup G)
    have hQ : Y.pCoreIn 2 ≤ sourceS L H :=
      d.parabolic_sylow_core_le_sourceS h.sylow_normalizes hTH i
    have hLiY : ![L,residual H] i ≤ Y := le_sup_left.trans (le_sup_left.trans le_sup_left)
    apply le_antisymm
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) (hQ.trans (hS i))
        (hLiY.trans (Y.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))))
    · exact pCoreIn_mono_of_normalizes hLiY (hn i)

/-- Source 5.2.7(3) for every concrete comparison, including both orientations
of the degree-two unitary extension. Normality of the enlarged core in the
whole overlap removes its outer parity; no containment of sourceS in Lᵢ is
assumed in that branch. -/
theorem Preparation.parabolic_sylow_core_eq_of_comparison
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect (residual H))
    (hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))) :
    ∀ i : Fin 2,
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊔ (T : Subgroup G)).pCoreIn 2 =
        (![L,residual H] i).pCoreIn 2 := by
  rcases d.sourceS_le_factors_or_unitaryExtension h hTH hp hc with hs | ⟨m,hm,he⟩
  · exact (d.ordinary_sylow_core_geometry h hTH hs).2
  intro i
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
  let Y := P ⊔ (T : Subgroup G)
  have hQ : Y.pCoreIn 2 ≤ sourceS L H :=
    d.parabolic_sylow_core_le_sourceS h.sylow_normalizes hTH i
  have hNY : Y ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hIP : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤ P := by
    fin_cases i
    · exact inf_le_left
    · exact inf_le_right
  have hQL : Y.pCoreIn 2 ≤ ![L,residual H] i :=
    d.unitaryExtension_normal_two_subgroup_le_factors h hTH hp
      (isPGroup_pCoreIn 2 Y) hQ (hIP.trans (le_sup_left.trans hNY)) m hm he i
  have hLiY : ![L,residual H] i ≤ Y := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hn : Y ≤ normalizer (![L,residual H] i : Set G) := by
    refine sup_le ((normal_subgroupOf_iff_le_normalizer
      (show ![L,residual H] i ≤ P from le_sup_left.trans le_sup_left)).mp
        ((d.hypothesisF11 h hTH).local_normal_in_parabolic i)) ?_
    fin_cases i
    · exact h.sylow_normalizes
    · exact hTH.trans (le_normalizer_residual H)
  exact le_antisymm
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y) hQL (hLiY.trans hNY))
    (pCoreIn_mono_of_normalizes hLiY hn)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
