module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallNormalizerRemoval
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalizerReplacement

/-!
# The complete small-component normalizer replacement

For the PSL3(3) and M11 branches, the actual saturated component radical is
normal in the original Sylow: it is the core of the GL2(3) intersection or
the Sylow intersection with the normal component. The selected local pair
also normalizes it. Adjoining this radical to the original normalizer family
therefore preserves the source setup and both starred conditions.

Source: Aschbacher--Smith 2.5.3(4), printed p.553. The earlier actual GL2(3)
intersection remains explicit; no radical, normalization or descent input
is assumed.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The original Sylow normalizes the small component radical in the contained branch. -/
theorem small_normalizer_contains_original_sylow
    (hG : IsQuasithin G) (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H))
    (e : ((M.subgroupOf H).subgroupOf D) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (S : Subgroup H) ≤ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H) := by
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  let I := (M.subgroupOf H).subgroupOf D
  let J := D ⊓ M.subgroupOf H
  let : D.Normal := small_component_normal hG hH D hD hm
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  have hPM : (P : Subgroup D) ≤ I := by
    rw [hP]
    intro d hd
    exact hSM (mem_map_of_mem H.subtype hd)
  have hQP : Q.subgroupOf D ≤ (P : Subgroup D) := by
    rw [hP]
    exact subgroupOf_mono D hQS
  have hRmap : (Q.subgroupOf D).map D.subtype = R := by
    rw [subgroupOf_map_subtype, inf_comm]
  have hInorm : (S : Subgroup H) ≤ normalizer (J : Set H) := by
    apply (le_inf le_normalizer_of_normal ?_).trans inf_normalizer_le_normalizer_inf
    exact (map_le_iff_le_comap.mp hSM).trans (M.subgroupOf H).le_normalizer
  change (S : Subgroup H) ≤ normalizer (R : Set H)
  rcases contained_component_radical_eq_core_or_sylow hpair hsat D hD hinside
      P hPM hQP e with he | he
  · have hRcore : R = J.pCoreIn 2 := by
      rw [← hRmap, he, map_pCoreIn_of_injective 2 I D.subtype D.subtype_injective]
      congr 1
      exact (subgroupOf_map_subtype (M.subgroupOf H) D).trans (inf_comm _ _)
    rw [hRcore]
    exact hInorm.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  · have hRS : R = D ⊓ (S : Subgroup H) := by
      rw [← hRmap, he, hP, subgroupOf_map_subtype, inf_comm]
    rw [hRS]
    exact (le_inf le_normalizer_of_normal (S : Subgroup H).le_normalizer).trans
      inf_normalizer_le_normalizer_inf

/-- The literal contained-normalizer replacement preserves the source hypotheses
and both stars, and removes the chosen small component. -/
theorem small_component_normalizer_source
    (hG : IsQuasithin G) (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11))
    (hinside : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H))
    (e : ((M.subgroupOf H).subgroupOf D) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    let R := D ⊓ (twoCore HU).subgroupOf H
    let X := (normalizer (R : Set H)).map H.subtype
    ∃ B' : Fin (n + 1) → Subgroup G,
      X < H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧
        K.map X.subtype ≤ centralizer (D.map H.subtype : Set G) ∧
        K.map X.subtype ≠ D.map H.subtype := by
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  let N := normalizer (R : Set H)
  let X := N.map H.subtype
  let I := (M.subgroupOf H).subgroupOf D
  let : D.Normal := small_component_normal hG hH D hD hm
  have hUR : HU.subgroupOf H ≤ N := by
    apply (le_inf le_normalizer_of_normal ?_).trans inf_normalizer_le_normalizer_inf
    intro a ha x
    exact le_normalizer_twoCore HU ha (x : G)
  have hSR : (S : Subgroup H) ≤ N := small_normalizer_contains_original_sylow
    hG hH hpair hsat D hD hm hinside S hSM hQS e
  obtain ⟨B', hX, hstar, hmax, hHUX, hSX, hp', hBX, hXnorm⟩ :=
    normalizer_replacement_preserves_source hH B hp hBH hHnorm hpair hbig hsat S hUS
      R inf_le_right hUR hSR
  have hDN : ¬ D ≤ N := by
    intro hDN
    let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
      Matrix.GeneralLinearGroup.three_isSolvable
    let : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    let f : D →* I := {
      toFun d := ⟨d, hinside (mem_map_of_mem H.subtype ⟨d.property, hDN d.property⟩)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective (f := f)
      (fun _ _ he => congrArg Subtype.val he)
    let : IsQuasisimple D := hD.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
    exact Group.IsPerfect.not_isSolvable D inferInstance
  have hXlt : X < H := by
    have hn : N < ⊤ := lt_top_iff_ne_top.mpr (fun he => hDN (he ▸ le_top))
    have hm := (map_lt_map_iff_of_injective H.subtype_injective).mpr hn
    simpa only [← MonoidHom.range_eq_map, H.range_subtype] using hm
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal D
  have hPM : (P : Subgroup D) ≤ I := by
    rw [hP]
    intro d hd
    exact hSM (mem_map_of_mem H.subtype hd)
  have hQP : Q.subgroupOf D ≤ (P : Subgroup D) := by
    rw [hP]
    exact subgroupOf_mono D hQS
  have hremain := small_normalizer_components_remain hG hH hpair hsat D hD hm
    hinside P hPM hQP e
  change ∃ B' : Fin (n + 1) → Subgroup G, _
  refine ⟨B', hXlt, hX, hstar, hmax, hHUX, hSX, hp', hBX, hXnorm, ?_⟩
  intro K hK
  let j : N ≃* X := N.equivMapOfInjective H.subtype H.subtype_injective
  let L := (K.map j.symm.toMonoidHom).map N.subtype
  obtain ⟨hL, hLC, hLD⟩ := hremain (K.map j.symm.toMonoidHom) (hK.map_equiv j.symm)
  have hj : H.subtype.comp (N.subtype.comp j.symm.toMonoidHom) = X.subtype := by
    ext x
    exact congrArg Subtype.val (j.apply_symm_apply x)
  have hLK : L.map H.subtype = K.map X.subtype := by
    change ((K.map j.symm.toMonoidHom).map N.subtype).map H.subtype = _
    rw [map_map, map_map, MonoidHom.comp_assoc, hj]
  refine ⟨⟨(map_subtype_le K).trans (map_subtype_le N), ?_⟩, ?_, ?_⟩
  · rw [← hLK]
    change IsComponent H ((L.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  · rw [← hLK]
    rintro a ⟨l, hl, rfl⟩ d ⟨t, ht, rfl⟩
    exact congrArg H.subtype (hLC hl t ht)
  · intro he
    exact hLD ((Subgroup.map_injective H.subtype_injective) (hLK.trans he))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
