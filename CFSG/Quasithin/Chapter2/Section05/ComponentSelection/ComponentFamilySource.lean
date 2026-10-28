module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalizerReplacement
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.ComponentFamilyNormalizer

/-!
# The source replacement for a normal selected-component product

If saturation contains Sylow subgroups of a selected component family whose
product is normal, its Sylow normalizer retains the actual finite normalizer
family, chosen pair, original Sylow and both starred conditions. Its
components descend to original components distinct from every selected
factor. Finite two-Schreier and evenness are proved internally.

This common source step serves the Bender family and the contained-normalizer
branches whose Borel intersection core is Sylow. Source: Aschbacher--Smith
2.5.3(4), printed pp.552--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The selected component subfamily is removed from the actual source replacement. -/
theorem exists_component_family_source_replacement
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H))
    (F : Set (Subgroup H)) (hF : ∀ D ∈ F, IsComponent H D)
    [(sSup F).Normal]
    (hcomp : ∀ D ∈ F, ∃ P : Sylow 2 D,
      (P : Subgroup D).map D.subtype ≤ (twoCore HU).subgroupOf H) :
    ∃ (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X ≤ H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧
          ∀ D ∈ F, K.map X.subtype ≠ D.map H.subtype := by
  let E := sSup F
  let Q := (twoCore HU).subgroupOf H
  have hQp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 HU).comap_subtype
  obtain ⟨P, hP⟩ := exists_component_family_sylow_eq_inf F hF Q hQp hcomp
  let V : Subgroup H := (P : Subgroup E).map E.subtype
  let N := normalizer (V : Set H)
  let X := N.map H.subtype
  have hVQ : V ≤ Q := hP.le.trans inf_le_right
  have hUR : HU.subgroupOf H ≤ N := by
    change HU.subgroupOf H ≤ normalizer (V : Set H)
    rw [show V = E ⊓ Q from hP]
    apply (le_inf le_normalizer_of_normal ?_).trans inf_normalizer_le_normalizer_inf
    intro a ha x
    exact le_normalizer_twoCore HU ha (x : G)
  have hVEq : V = E ⊓ (S : Subgroup H) := by
    have hi : (S : Subgroup H).subgroupOf E = (P : Subgroup E) :=
      P.is_maximal' S.isPGroup'.comap_subtype
        (map_le_iff_le_comap.mp (hVQ.trans hQS))
    change (P : Subgroup E).map E.subtype = _
    rw [← hi, subgroupOf_map_subtype, inf_comm]
  have hSR : (S : Subgroup H) ≤ N := by
    change (S : Subgroup H) ≤ normalizer (V : Set H)
    rw [hVEq]
    exact (le_inf le_normalizer_of_normal (S : Subgroup H).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨B', hX, hstar, hmax, hHUX, hSX, hp', hBX, hXnorm⟩ :=
    normalizer_replacement_preserves_source hH B hp hBH hHnorm hpair hbig hsat S hUS
      V hVQ hUR hSR
  have heven : ∀ D ∈ F, 2 ∣ Nat.card (D ⧸ center D) := by
    intro D hd
    let : IsQuasisimple D := (hF D hd).2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Group.IsPerfect (D ⧸ center D) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center D))
    by_contra hn
    let : Group.IsSolvable (D ⧸ center D) := odd_order_theorem _
      (Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he)))
    exact Group.IsPerfect.not_isSolvable (D ⧸ center D) inferInstance
  have hremain := components_descend_from_component_family_normalizer
    (ChapterI.SylowAutomorphisms.hasTwoSchreier H) F hF heven P
  refine ⟨X, B', map_subtype_le _, hX, hstar, hmax, hHUX, hSX, hp', hBX, hXnorm, ?_⟩
  intro K hK
  let j : N ≃* X := N.equivMapOfInjective H.subtype H.subtype_injective
  let L := (K.map j.symm.toMonoidHom).map N.subtype
  obtain ⟨hL, _hLC, hLF⟩ := hremain (K.map j.symm.toMonoidHom) (hK.map_equiv j.symm)
  have hj : H.subtype.comp (N.subtype.comp j.symm.toMonoidHom) = X.subtype := by
    ext x
    exact congrArg Subtype.val (j.apply_symm_apply x)
  have hLK : L.map H.subtype = K.map X.subtype := by
    change ((K.map j.symm.toMonoidHom).map N.subtype).map H.subtype = _
    rw [map_map, map_map, MonoidHom.comp_assoc, hj]
  refine ⟨⟨(map_subtype_le K).trans (map_subtype_le N), ?_⟩, ?_⟩
  · rw [← hLK]
    change IsComponent H ((L.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  · intro D hd he
    exact hLF D hd ((Subgroup.map_injective H.subtype_injective) (hLK.trans he))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
