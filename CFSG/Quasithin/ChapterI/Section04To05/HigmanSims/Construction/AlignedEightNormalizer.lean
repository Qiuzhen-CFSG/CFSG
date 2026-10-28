module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AlignedElementarySixteen
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreElementaryBound
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedEightCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreInvolutionFusion

/-!
# A marked E16 with its actual nonseed E8 and full centralizer

The elementary subgroup bound identifies the whole intersection of the
aligned sixteen with its first point core as the nonseed eight generated
by the original plane and first lift. The full-H orbit and centralizer
calculations then apply to that literal eight. The second point-core lift
is retained as a seed-class involution outside it.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- Original HS data yield an actual E16 containing a nonseed eight in one
original point core, with its full centralizer and normalizer orders, and
a known seed-class involution outside that eight. -/
theorem TypeAt.exists_aligned_eight_normalizer (h : TypeAt z V) :
    ∃ (u b : G) (A : Subgroup G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      E.val = A ⊓ (involutionCentralizer u).pCoreIn 2 ∧
      E.val ∉ pointCoreSeedOrbit u V ∧
      A ≤ centralizer (E.val : Set G) ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      b ∈ A ∧ b ∉ E.val ∧ orderOf b = 2 ∧ IsConj b z := by
  obtain ⟨W, A, u, v, a, b, hWV, hW4, hAE, hA16, hWA, hAC, hAP,
    huW, hvW, hu1, hv1, huv, haQ, hbQ, haP, hbP, habP, hjoin⟩ :=
    h.exists_aligned_elementary_sixteen
  let huT := h.at_seed_point u (hWV huW) hu1
  let hvT := h.at_seed_point v (hWV hvW) hv1
  let Q := (involutionCentralizer u).pCoreIn 2
  have hVQ : V ≤ Q := by
    change V ≤ (pCore 2 (involutionCentralizer u)).map (involutionCentralizer u).subtype
    rw [← huT.centralizer_fitting]
    exact huT.seed_le_core
  let B := W ⊔ zpowers a
  have haA : a ∈ A := by
    rw [hjoin]
    exact (show zpowers a ≤ W ⊔ (zpowers a ⊔ zpowers b) from
      le_sup_left.trans le_sup_right) (mem_zpowers a)
  have hbA : b ∈ A := by
    rw [hjoin]
    exact (show zpowers b ≤ W ⊔ (zpowers a ⊔ zpowers b) from
      le_sup_right.trans le_sup_right) (mem_zpowers b)
  let := hAE
  have hBA : B ≤ A := sup_le hWA (zpowers_le.mpr haA)
  have hBQ : B ≤ Q := sup_le (hWV.trans hVQ) (zpowers_le.mpr haQ)
  have hBE : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.of_injective (inclusion hBA) (inclusion_injective hBA)
  have hVP : V ≤ (normalizer (V : Set G)).pCoreIn 2 := by
    change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.normalizer_fitting]
    exact h.seed_le_normalizer_core
  have hB8 : Nat.card B = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W a
      (elemPow_eq_one_of_isElementaryAbelian a haA)
      (fun hh => haP (hVP (hWV hh))) (centralizer_le_normalizer _ (hAC haA)), hW4]
  have hBcap : B = A ⊓ Q := by
    apply eq_of_le_of_card_ge (le_inf hBA hBQ)
    let D := (A ⊓ Q : Subgroup G).subgroupOf Q
    let j : D →* A := {
      toFun x := ⟨x, x.property.1⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hj : Function.Injective j := by
      intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : A => (a : G)) he
    let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective j hj
    have hs : CoreShape Q := (huT.centralizer_core.of_equiv
      (MulEquiv.subgroupCongr huT.centralizer_fitting)).of_equiv
        ((pCore 2 (involutionCentralizer u)).equivMapOfInjective
          (involutionCentralizer u).subtype (involutionCentralizer u).subtype_injective)
    have hb := hs.elementary_card_le_eight D inferInstance
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ Q ≤ Q from inf_le_right)).toEquiv] at hb
    exact hB8 ▸ hb
  let E : pointCoreEights u := ⟨B, hBQ, (show W ≤ B from le_sup_left) huW, hBE, hB8⟩
  have hBV : B ⊓ V = W := by
    apply le_antisymm
    · intro x hx
      exact hAP ▸ (show x ∈ A ⊓ (normalizer (V : Set G)).pCoreIn 2 from
        ⟨hBA hx.1, hVP hx.2⟩)
    · exact le_inf le_sup_left hWV
  have hBn : E.val ∉ pointCoreSeedOrbit u V := by
    rintro ⟨g, hg⟩
    change V.map (MulAut.conj (g : G)).toMonoidHom = B at hg
    by_cases hn : (g : G) ∈ normalizer (V : Set G)
    · have he : B = V := hg.symm.trans (mem_normalizer_iff_map_conj_eq.mp hn)
      have hc := congrArg (fun S : Subgroup G => Nat.card S) hBV
      rw [he, inf_idem, h.seed_card, hW4] at hc
      omega
    · have he := huT.seed_conjugate_intersection g g.property hn
      rw [hg, inf_comm, hBV] at he
      have hc := congrArg (fun S : Subgroup G => Nat.card S) he
      rw [hW4, Nat.card_zpowers, huT.involution] at hc
      omega
  have hbout : b ∉ E.val := by
    intro hh
    have hboth : b ∈ (involutionCentralizer u).pCoreIn 2 ⊓
        (involutionCentralizer v).pCoreIn 2 := ⟨hBQ hh, hbQ⟩
    rw [h.distinct_point_cores_intersection u v (hWV huW) (hWV hvW) hu1 hv1 huv] at hboth
    exact hbP (hVP hboth)
  have hb2 : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hbA) (fun he => hbP (he ▸ one_mem _))
  have hbv : IsConj b v := hvT.centralizer_core_involution_isConj b hbQ hb2
  have hvz : IsConj v z := h.centralizer_core_involution_isConj v
    (by
      change v ∈ (pCore 2 (involutionCentralizer z)).map (involutionCentralizer z).subtype
      rw [← h.centralizer_fitting]
      exact h.seed_le_core (hWV hvW)) hvT.involution
  refine ⟨u, b, A, E, hWV huW, hu1, huT, hAE, hA16, hBcap, hBn, ?_,
    huT.point_core_nonseed_eight_centralizer_card E hBn,
    huT.point_core_nonseed_eight_normalizer_card E hBn, hbA, hbout, hb2, hbv.trans hvz⟩
  intro x hx y hy
  exact setLike_mul_comm (hBA hy) hx

end CFSG.Quasithin.HigmanSims
