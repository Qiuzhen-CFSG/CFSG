module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalizerReplacement
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderSource
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.ComponentFamilyNormalizer

/-!
# Removing the full Bender component subfamily

Take the characteristic product E of all Bender components. The original
saturated pair contains a Sylow subgroup of every such component by the
proved 2.5.3(3), so V=E∩Q is a Sylow subgroup of E. Both the pair and the
original Sylow normalize V. Its normalizer therefore retains the literal
source normalizer family and both starred conditions.

The selected-component descent theorem makes every replacement component
an original component centralizing E. It cannot itself be a Bender model,
as then it would lie in E and be abelian. Finite two-Schreier and the even
order of each simple component quotient are discharged internally. No
restriction to groups whose entire layer is Bender is needed.

Source: Aschbacher--Smith 2.5.3(4), printed p.552, its first reduction.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- Remove all Bender components, preserving the original normalizer family,
selected pair, original Sylow and both stars. Every remaining component is
an actual original component. -/
theorem exists_bender_family_replacement
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
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
    (hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H)) :
    ∃ (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X ≤ H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      HU ≤ X ∧ (S : Subgroup H).map H.subtype ≤ X ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧ ¬ ClassificationModels.IsBenderModel K := by
  let F : Set (Subgroup H) := {D | IsComponent H D ∧ ClassificationModels.IsBenderModel D}
  let E := sSup F
  let : E.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro e
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro D hd
    exact map_le_iff_le_comap.mp (le_sSup
      ⟨hd.1.map_equiv e, hd.2.of_mulEquiv (e.subgroupMap D).symm⟩)
  let Q := (twoCore HU).subgroupOf H
  have hQp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 HU).comap_subtype
  have hcomp : ∀ D ∈ F, ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype ≤ Q := by
    intro D hd
    obtain ⟨P, hP⟩ := lemma_2_5_3_three hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
      hpair hsat D hd.1 hd.2
    exact ⟨P, map_le_iff_le_comap.mp (hP.le.trans inf_le_right)⟩
  obtain ⟨P, hP⟩ := exists_component_family_sylow_eq_inf F (fun _ h => h.1) Q hQp hcomp
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
    let : IsQuasisimple D := hd.1.2
    let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
    let : Group.IsPerfect (D ⧸ center D) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center D))
    by_contra hn
    let : Group.IsSolvable (D ⧸ center D) := odd_order_theorem _
      (Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he)))
    exact Group.IsPerfect.not_isSolvable (D ⧸ center D) inferInstance
  have hremain := components_descend_from_component_family_normalizer
    (ChapterI.SylowAutomorphisms.hasTwoSchreier H) F (fun _ h => h.1) heven P
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
  · intro hKb
    let e : K ≃* L := (K.equivMapOfInjective j.symm.toMonoidHom j.symm.injective).trans
      ((K.map j.symm.toMonoidHom).equivMapOfInjective N.subtype N.subtype_injective)
    exact hLF L ⟨hL, hKb.of_mulEquiv e.symm⟩ rfl

/-- The Bender-free replacement exists on the original normalizer-family
hypotheses; the saturated pair and compatible original Sylow are constructed. -/
theorem exists_bender_free_source_replacement
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G)) :
    ∃ (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X ≤ H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype ≤ X) ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K →
        IsComponentIn (K.map X.subtype) H ∧ ¬ ClassificationModels.IsBenderModel K := by
  obtain ⟨U, HU, hpair, hbig, hsat⟩ := exists_saturated_pair_preserving_star hH
  obtain ⟨R, hUR, hRb⟩ := beta_exists_sylow hpair.1.1 hpair.1.2.2.2.1
  obtain ⟨S, hRS, _hSb⟩ := beta_exists_sylow hRb ((map_subtype_le _).trans hpair.2)
  have hUS : U ≤ (S : Subgroup H).map H.subtype := hUR.trans hRS
  have hQSm : twoCore HU ≤ (S : Subgroup H).map H.subtype :=
    (pCoreIn_le_sylow HU R).trans hRS
  have hQS : (twoCore HU).subgroupOf H ≤ (S : Subgroup H) := by
    intro x hx
    obtain ⟨s, hs, he⟩ := hQSm hx
    exact (Subtype.ext he : s = x) ▸ hs
  obtain ⟨X, B', hXH, hX, hstar, hmax, _hHU, hSX, hp', hBX, hXnorm, hcomp⟩ :=
    exists_bender_family_replacement hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
      hpair hbig hsat S hUS hQS
  exact ⟨X, B', hXH, hX, hstar, hmax, ⟨S, hSX⟩, hp', hBX, hXnorm, hcomp⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
