module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourShiftedGeneration
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.GenerationSource

/-!
# E.6.26 with the original E-generation witness

A normal subgroup of H containing J(P) changes its Sylow intersection from P
to S. E.6.1 and J_j(S)≤C(V) give all the small-codimension centralizer bounds
for Ω₁Z(J_j(S)). The shifted E.5 argument uses H's own E-generation witness
and proves H≤M. No generation parameter of the normal subgroup is assumed.

Source application: Aschbacher--Smith 6.1.4, printed p.665.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal normal-intersection variant of E.6.26. All elementary
families and E-members belong to the original H. -/
theorem source_E_6_26_of_normal_intersection
    {κ : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 κ T M V) {j : ℕ} (hjpos : 0 < j)
    (H : Subgroup G) (P : Sylow 2 H) (N : Subgroup H) [N.Normal]
    (hgen : IsEGenerated j H)
    (hJN : thompsonJ (P : Subgroup H) 0 ≤ N)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤
      ((P : Subgroup H) ⊓ N).map H.subtype)
    (hAT : ((P : Subgroup H) ⊓ N).map H.subtype ≤ T)
    (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ (((P : Subgroup H) ⊓ N).map H.subtype) j ≤
      centralizer (V : Set G)) :
    H ≤ M ∧ normalizer (((P : Subgroup H) ⊓ N).map H.subtype : Set G) ≤ M := by
  let S := (P : Subgroup H) ⊓ N
  let A := S.map H.subtype
  let D := higherThompsonCenter S j
  have hVA : V ≤ A := h.le_sylowCentralizer.trans hQA
  have hr := rank_bound h hVA hj
  have hVD : V ≤ higherThompsonCenter A j := by
    change V ≤ omegaOneCenterAmbient (thompsonJ A j)
    rw [← (lemma_B_2_3_2 A (le_refl j) hr).2]
    intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
      ⟨hVA hx,(le_centralizer_iff.mp hJ) hx⟩
      (by let := h.elementary; exact elemPow_eq_one_of_isElementaryAbelian x hx)
  have hDmap : D.map H.subtype = higherThompsonCenter A j := by
    dsimp [D,higherThompsonCenter,A]
    rw [thompsonJ_map_injective H.subtype H.subtype_injective,
      omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
  have hJS : thompsonJ (P : Subgroup H) 0 = thompsonJ S 0 :=
    congrArg sSup (maximal_thompsonFamily_inf_eq (P : Subgroup H) N hJN)
  have hN := normalizer_thompson_le_of_control h hj hQA hAT hJ
  have hNM : normalizer (thompsonJ (P : Subgroup H) 0 : Set H) ≤ M.comap H.subtype := by
    apply map_le_iff_le_comap.mp
    apply (le_normalizer_map H.subtype).trans
    rw [hJS,←thompsonJ_map_injective H.subtype H.subtype_injective]
    exact hN
  have hrS : j < twoRank S := by
    have he : twoRank A = twoRank S := twoRank_map_injective H.subtype H.subtype_injective S
    exact he ▸ hr
  have hwhole : M.comap H.subtype = ⊤ := by
    apply eq_top_of_shifted_thompson_centralizers P N (M.comap H.subtype)
      hjpos hgen hJN hrS hNM
    intro d hd hindex
    have hi : Nat.log 2 ((V ⊓ d.map H.subtype).relIndex V) ≤ j := by
      rw [inf_relIndex_left]
      have hv : V ≤ D.map H.subtype := hDmap.symm ▸ hVD
      have hi := relIndex_le_of_le_right (H := d.map H.subtype) hv
        (show (d.map H.subtype).relIndex (D.map H.subtype) ≠ 0 from index_ne_zero_of_finite)
      have hl := Nat.log_mono_right (b := 2) hi
      rw [relIndex_map_map_of_injective _ _ H.subtype_injective] at hl
      exact hl.trans hindex
    have hc : centralizer (V ⊓ d.map H.subtype : Set G) ≤ M :=
      (centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
        (lt_of_le_of_lt (by exact_mod_cast hi) hj)).trans h.normalizer_le
    apply map_le_iff_le_comap.mp
    exact (map_centralizer_le_centralizer_image (d : Set H) H.subtype).trans
      ((centralizer_le inf_le_right).trans hc)
  refine ⟨?_,normalizer_le_of_control h hj hQA hAT hJ⟩
  intro x hx
  exact show (⟨x,hx⟩ : H) ∈ M.comap H.subtype from hwhole ▸ mem_top _

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
