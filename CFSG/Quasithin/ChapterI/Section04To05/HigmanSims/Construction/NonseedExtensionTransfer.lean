module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExtensionCentralizers
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedConjugateTypes

/-!
# Extension structure for every original nonseed eight

The source constructs one pair of elementary-sixteen extensions, with exact
ambient centralizers and original point-core intersections. Actual seed
fusion moves its marked point to the original one. Its centralizer order
distinguishes its eight from every seed conjugate. The proved transitivity
on the ten nonseed eights then transports these facts to any specified
nonseed eight and any specified elementary-sixteen extension of it.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private def ExtensionFacts (u : G) (E : Subgroup G) : Prop :=
  ∀ A : Subgroup G, E ≤ A → IsElementaryAbelian 2 A → Nat.card A = 16 →
    (involutionCentralizer u).pCoreIn 2 ≤ normalizer (A : Set G) ∧
      centralizer (A : Set G) = A ∧ A ⊓ (involutionCentralizer u).pCoreIn 2 = E

omit [Finite G] in
private theorem centralizer_image (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  exact map_centralizer_equiv (A : Set G) e

private theorem point_core_image (u : G) (e : G ≃* G) :
    ((involutionCentralizer u).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer (e u)).pCoreIn 2 := by
  rw [map_pCoreIn_of_ker_isPGroup _ (by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    exact IsPGroup.of_subsingleton 2 (⊥ : Subgroup G)),
    map_centralizer_equiv, Set.image_singleton]

private theorem facts_map (u : G) (E : Subgroup G) (hf : ExtensionFacts u E)
    (e : G ≃* G) : ExtensionFacts (e u) (E.map e.toMonoidHom) := by
  intro A hEA hAe hA16
  let D := A.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 A := hAe
  have hED : E ≤ D := by
    intro x hx
    exact mem_map_equiv.mpr (hEA (mem_map_of_mem e.toMonoidHom hx))
  have hDe : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.symm.toMonoidHom
  have hD16 : Nat.card D = 16 := (card_map_of_injective e.symm.injective).trans hA16
  obtain ⟨hQN, hCD, hDQ⟩ := hf D hED hDe hD16
  have hDmap : D.map e.toMonoidHom = A := by
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.apply_symm_apply x
    rw [he, map_id]
  refine ⟨?_, ?_, ?_⟩
  · have hh := map_mono (f := e.toMonoidHom) hQN
    rwa [point_core_image, map_equiv_normalizer_eq, hDmap] at hh
  · have hh := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) hCD
    rwa [centralizer_image, hDmap] at hh
  · have hh := congrArg (fun S : Subgroup G => S.map e.toMonoidHom) hDQ
    rwa [map_inf _ _ _ e.injective, point_core_image, hDmap] at hh

private theorem seed_centralizer_card (h : TypeAt z V) :
    Nat.card (centralizer (V : Set G)) = 64 := by
  rw [h.seed_centralizer, card_map_of_injective (normalizer (V : Set G)).subtype_injective,
    ← h.normalizer_fitting]
  exact h.normalizer_core_card

private theorem facts_at_original_point (h : TypeAt z V) :
    ∃ E : pointCoreEights z, E.val ∉ pointCoreSeedOrbit z V ∧ ExtensionFacts z E.val := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, _,
    _, _, _, _, _, _, _, _, hAe, hA16, hBe, hB16, _, _, hQN, hCA, hCB, hAQ, hBQ, hall⟩ :=
    h.exists_selfcentralizing_nonseed_extensions
  have hf : ExtensionFacts u E.val := by
    intro F hEF hFe hF16
    rcases (hall F).mp ⟨hEF, hFe, hF16⟩ with rfl | rfl
    · exact ⟨hQN.trans inf_le_left, hCA, hAQ⟩
    · exact ⟨hQN.trans inf_le_right, hCB, hBQ⟩
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  obtain ⟨m, hm⟩ := h.seed_transitive (⟨u, huV⟩ : V) ⟨z, h.involution_mem_seed⟩
    (fun he => hu1 (congrArg Subtype.val he)) (fun he => hz1 (congrArg Subtype.val he))
  let e := MulAut.conj (m : G)
  have hu : e u = z := congrArg Subtype.val hm
  have hQ : ((involutionCentralizer u).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer z).pCoreIn 2 := by rw [point_core_image, hu]
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  let F : pointCoreEights z := ⟨E.val.map e.toMonoidHom,
    (map_mono E.property.1).trans_eq hQ,
    ⟨u, E.property.2.1, hu⟩, IsElementaryAbelian.map e.toMonoidHom,
    (card_map_of_injective e.injective).trans E.property.2.2.2⟩
  have hF32 : Nat.card (centralizer (F.val : Set G)) = 32 := by
    change Nat.card (centralizer (E.val.map e.toMonoidHom : Set G)) = 32
    rw [← centralizer_image, card_map_of_injective e.injective]
    exact hK32
  have hFn : F.val ∉ pointCoreSeedOrbit z V := by
    rintro ⟨g, hg⟩
    change V.map (MulAut.conj (g : G)).toMonoidHom = F.val at hg
    have hh := seed_centralizer_card (h.conj (g : G))
    rw [hg, hF32] at hh
    contradiction
  refine ⟨F, hFn, ?_⟩
  have hh := facts_map u E.val hf e
  rwa [hu] at hh

/-- Every literal elementary sixteen containing any original nonseed eight
is normalized by the original point core, is self-centralizing in the full
ambient group, and meets that point core in exactly the specified eight. -/
theorem TypeAt.nonseed_eight_extension_structure (h : TypeAt z V)
    (E : pointCoreEights z) (hEn : E.val ∉ pointCoreSeedOrbit z V)
    (A : Subgroup G) (hEA : E.val ≤ A) (hAe : IsElementaryAbelian 2 A)
    (hA16 : Nat.card A = 16) :
    (involutionCentralizer z).pCoreIn 2 ≤ normalizer (A : Set G) ∧
      centralizer (A : Set G) = A ∧ A ⊓ (involutionCentralizer z).pCoreIn 2 = E.val := by
  obtain ⟨F, hFn, hf⟩ := facts_at_original_point h
  obtain ⟨g, hg⟩ := h.point_core_nonseed_eights_transitive F E hFn hEn
  have hz : (MulAut.conj (g : G)) z = z := by
    change (g : G) * z * (g : G)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have hh := facts_map z F.val hf (MulAut.conj (g : G))
  rw [hz, hg] at hh
  exact hh A hEA hAe hA16

end CFSG.Quasithin.HigmanSims
