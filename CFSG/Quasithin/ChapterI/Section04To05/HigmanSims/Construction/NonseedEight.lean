module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AlignedElementarySixteen
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedIntersections
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Injective

/-!
# An actual nonseed elementary eight in an HS point core

The aligned elementary sixteen contains a plane W of the original seed and
an external involution in the point core at u∈W. Their join is an elementary
eight in that actual point core, meeting V exactly in W. The original
five-seed intersection theorem excludes it from the centralizer orbit of V.
Conjugating by an actual seed normalizer moves u to the originally marked z.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem exists_at_some_point (h : TypeAt z V) :
    ∃ (u : G) (E : Subgroup G), u ∈ V ∧ u ≠ 1 ∧
      E ≤ (involutionCentralizer u).pCoreIn 2 ∧ u ∈ E ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ Nat.card (E ⊓ V : Subgroup G) = 4 := by
  obtain ⟨W, A, u, v, a, b, hWV, hW4, hAE, hA16, hWA, hAC, hAP,
    huW, hvW, hu1, hv1, huv, haQ, hbQ, haP, hbP, habP, hjoin⟩ :=
    h.exists_aligned_elementary_sixteen
  let E := W ⊔ zpowers a
  have haA : a ∈ A := by
    rw [hjoin]
    exact (show zpowers a ≤ W ⊔ (zpowers a ⊔ zpowers b) from
      le_sup_left.trans le_sup_right) (mem_zpowers a)
  have hEA : E ≤ A := sup_le hWA (zpowers_le.mpr haA)
  let := hAE
  have hEE : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_injective (inclusion hEA) (inclusion_injective hEA)
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haA
  have hVP : V ≤ (normalizer (V : Set G)).pCoreIn 2 := by
    change V ≤ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.normalizer_fitting]
    exact h.seed_le_normalizer_core
  have haW : a ∉ W := fun hh => haP (hVP (hWV hh))
  have hE8 : Nat.card E = 8 := by
    rw [card_sup_zpowers_of_normalizing_involution W a ha2 haW
      (centralizer_le_normalizer _ (hAC haA)), hW4]
  have hEV : E ⊓ V = W := by
    apply le_antisymm
    · intro x hx
      exact hAP ▸ (show x ∈ A ⊓ (normalizer (V : Set G)).pCoreIn 2 from
        ⟨hEA hx.1, hVP hx.2⟩)
    · exact le_inf le_sup_left hWV
  have huT := h.at_seed_point u (hWV huW) hu1
  have hVQ : V ≤ (involutionCentralizer u).pCoreIn 2 := by
    change V ≤ (pCore 2 (involutionCentralizer u)).map (involutionCentralizer u).subtype
    rw [← huT.centralizer_fitting]
    exact huT.seed_le_core
  exact ⟨u, E, hWV huW, hu1, sup_le (hWV.trans hVQ) (zpowers_le.mpr haQ),
    (show W ≤ E from le_sup_left) huW, hEE, hE8, hEV ▸ hW4⟩

/-- Original HS data construct an elementary eight in the original marked
point core which is outside the entire original centralizer orbit of the seed. -/
theorem TypeAt.exists_nonseed_point_core_eight (h : TypeAt z V) :
    ∃ E : Subgroup G, E ≤ (involutionCentralizer z).pCoreIn 2 ∧ z ∈ E ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧
      Nat.card (E ⊓ V : Subgroup G) = 4 ∧
      ∀ g : involutionCentralizer z, E ≠ V.map (MulAut.conj (g : G)).toMonoidHom := by
  obtain ⟨u, E, hu, hu1, hEQ, huE, hEE, hE8, hEV4⟩ := exists_at_some_point h
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  obtain ⟨g, hgu⟩ := h.seed_transitive ⟨u, hu⟩ ⟨z, h.involution_mem_seed⟩
    (fun he => hu1 (congrArg Subtype.val he))
    (fun he => hz1 (congrArg Subtype.val he))
  let e := MulAut.conj (g : G)
  have heu : e u = z := congrArg Subtype.val hgu
  have heV : V.map e.toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp g.property
  have heH : (involutionCentralizer u).map e.toMonoidHom = involutionCentralizer z := by
    rw [← heu]
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      ← e.injective.eq_iff]
    simp only [map_mul, e.apply_symm_apply]
  have heQ : ((involutionCentralizer u).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer z).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup _ (by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      exact IsPGroup.of_subsingleton 2 (⊥ : Subgroup G)), heH]
  let F := E.map e.toMonoidHom
  have hFQ : F ≤ (involutionCentralizer z).pCoreIn 2 := heQ ▸ map_mono hEQ
  have hzF : z ∈ F := ⟨u, huE, heu⟩
  let := hEE
  have hFE : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hF8 : Nat.card F = 8 := by rw [card_map_of_injective e.injective, hE8]
  have hFV4 : Nat.card (F ⊓ V : Subgroup G) = 4 := by
    rw [← heV, ← map_inf _ _ _ e.injective, card_map_of_injective e.injective]
    exact hEV4
  refine ⟨F, hFQ, hzF, hFE, hF8, hFV4, ?_⟩
  intro k hk
  by_cases hkN : (k : G) ∈ normalizer (V : Set G)
  · have heF : F = V := hk.trans (mem_normalizer_iff_map_conj_eq.mp hkN)
    rw [heF, inf_idem, h.seed_card] at hFV4
    omega
  · have he := h.seed_conjugate_intersection k k.property hkN
    rw [← hk, inf_comm] at he
    rw [he, Nat.card_zpowers, h.involution] at hFV4
    omega

end CFSG.Quasithin.HigmanSims
