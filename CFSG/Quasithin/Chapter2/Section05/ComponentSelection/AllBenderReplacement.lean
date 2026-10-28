module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MaximalPairBase
public import Theory.GroupTheory.GeneralizedFitting.LayerSylowContainment

/-!
# The actual layer-normalizer replacement when all components are Bender

Choose a saturated local pair above a globally largest base when needed.
If all components of H are Bender groups, 2.5.3(3) puts a Sylow subgroup
of the full layer in its core Q. Set W=Q intersect E(H). It is the layer
Sylow subgroup, so an original Sylow of H containing Q normalizes W.
The original local pair and both starred conditions survive in N_H(W).
Adjoining W to the original normalizer-intersection family gives the same
literal source form in the replacement, including containment of every
old two-subgroup. This is the input for the component-free contradiction.

Source: Aschbacher--Smith 2.5.3(4), printed p.552.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

omit [Finite G] in
private theorem normalizer_family_cons {n : ℕ} (B : Fin n → Subgroup G)
    (W X : Subgroup G) (hX : X = (⨅ i, normalizer (B i : Set G)) ⊓ normalizer (W : Set G))
    (hp : ∀ i, IsPGroup 2 (B i)) (hWp : IsPGroup 2 W)
    (hB : ∀ i, B i ≤ X) (hW : W ≤ X) :
    (∀ i, IsPGroup 2 (Fin.cases W B i : Subgroup G)) ∧
      (∀ i, Fin.cases W B i ≤ X) ∧
      X = ⨅ i, normalizer ((Fin.cases W B i : Subgroup G) : Set G) := by
  refine ⟨fun i => Fin.cases hWp hp i, fun i => Fin.cases hW hB i, ?_⟩
  rw [hX]
  apply le_antisymm
  · exact le_iInf fun i => Fin.cases inf_le_right
      (fun j => inf_le_left.trans (iInf_le _ j)) i
  · exact le_inf (le_iInf fun i => iInf_le _ i.succ) (iInf_le _ 0)

/-- The full source replacement has the same normalizer-intersection
form and preserves both stars; its layer Sylow is specified by actual maps. -/
theorem exists_all_bender_layer_replacement
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (hall : ∀ D : Subgroup H, IsComponent H D → ClassificationModels.IsBenderModel D) :
    ∃ (P : Sylow 2 (componentLayer H)) (X : Subgroup G) (B' : Fin (n + 1) → Subgroup G),
      X = (normalizer ((P : Subgroup (componentLayer H)).map
        (componentLayer H).subtype : Set H)).map H.subtype ∧
      X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      (∀ i, IsPGroup 2 (B' i)) ∧ (∀ i, B' i ≤ X) ∧
      X = ⨅ i, normalizer (B' i : Set G) := by
  obtain ⟨U, HU, hpair, hbig, hsat⟩ := exists_saturated_pair_preserving_star hH
  obtain ⟨R, hUR, hRb⟩ := beta_exists_sylow hpair.1.1 hpair.1.2.2.2.1
  obtain ⟨S, hRS, _hSb⟩ := beta_exists_sylow hRb ((map_subtype_le _).trans hpair.2)
  have hUS : U ≤ (S : Subgroup H).map H.subtype := hUR.trans hRS
  have hQS : twoCore HU ≤ (S : Subgroup H).map H.subtype :=
    (pCoreIn_le_sylow HU R).trans hRS
  let E := componentLayer H
  let Q := (twoCore HU).subgroupOf H
  have hQp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 HU).comap_subtype
  have hcomp : ∀ D : Subgroup H, IsComponent H D →
      ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype ≤ Q := by
    intro D hD
    obtain ⟨P, hP⟩ := lemma_2_5_3_three hG T₀ hM hT₀M hunique hH B hp hBH
      hHnorm hpair hsat D hD (hall D hD)
    exact ⟨P, map_le_iff_le_comap.mp (hP.le.trans inf_le_right)⟩
  obtain ⟨P, hP⟩ := exists_layer_sylow_eq_inf Q hQp hcomp
  let V : Subgroup H := (P : Subgroup E).map E.subtype
  let W := V.map H.subtype
  let X := H ⊓ normalizer (W : Set G)
  have hVE : V ≤ E := map_subtype_le _
  have hVQ : V ≤ Q := hP.le.trans inf_le_right
  have hWH : W ≤ H := map_subtype_le V
  have hWQ : W ≤ twoCore HU := map_le_iff_le_comap.mpr hVQ
  have hHQ : HU ≤ normalizer (W : Set G) := by
    have hn : HU.subgroupOf H ≤ normalizer (V : Set H) := by
      rw [show V = E ⊓ Q from hP]
      apply (le_inf le_normalizer_of_normal ?_).trans inf_normalizer_le_normalizer_inf
      intro a ha x
      exact le_normalizer_twoCore HU ha (x : G)
    intro a ha
    exact V.le_normalizer_map H.subtype ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
  have hQHU : twoCore HU ≤ HU := pCoreIn_le 2 HU
  have hHUX : HU ≤ X := le_inf hpair.2 hHQ
  have hQSin : Q ≤ (S : Subgroup H) := by
    intro x hx
    obtain ⟨s, hs, he⟩ := hQS hx
    exact (Subtype.ext he : s = x) ▸ hs
  have hVEq : V = E ⊓ (S : Subgroup H) := by
    have hi : (S : Subgroup H).subgroupOf E = (P : Subgroup E) :=
      P.is_maximal' S.isPGroup'.comap_subtype
        (map_le_iff_le_comap.mp (hVQ.trans hQSin))
    change (P : Subgroup E).map E.subtype = _
    rw [← hi, subgroupOf_map_subtype, inf_comm]
  have hSX : (S : Subgroup H).map H.subtype ≤ X := by
    refine le_inf (map_subtype_le _) ?_
    have hn : (S : Subgroup H) ≤ normalizer (V : Set H) := by
      rw [hVEq]
      exact (le_inf le_normalizer_of_normal (S : Subgroup H).le_normalizer).trans
        inf_normalizer_le_normalizer_inf
    exact (map_mono hn).trans (V.le_normalizer_map H.subtype)
  have hcoreX : twoCore X ≠ ⊥ := by
    have hQH : twoCore H ≤ twoCore HU := hsat _ (pCoreIn_le 2 H)
      (isPGroup_pCoreIn 2 H) (hpair.2.trans (le_normalizer_twoCore H))
    have hcore : twoCore H ≤ twoCore X := le_pCoreIn_of_normalizes
      (isPGroup_pCoreIn 2 H) (hQH.trans (hQHU.trans hHUX))
      (inf_le_left.trans (le_normalizer_twoCore H))
    intro hb
    have hg : H ∈ gamma (Chapter1.He G) M := hH.elim (fun h => h.1.1) (fun h => h.1)
    exact hg.1 (bot_unique (hb ▸ hcore))
  obtain ⟨hX, _hSyl, _hSylM, hstar, hmax⟩ := replacement_preserves_stars
    hH hpair hbig S hUS hHUX hSX hcoreX
  let B' : Fin (n + 1) → Subgroup G := Fin.cases W B
  have hBX : ∀ i, B i ≤ X := by
    intro i
    have hnorm : H ≤ normalizer (B i : Set G) := hHnorm.le.trans (iInf_le _ i)
    have hBcore := hsat (B i) (hBH i) (hp i) (hpair.2.trans hnorm)
    exact hBcore.trans (hQHU.trans hHUX)
  have hfamily := normalizer_family_cons B W X
    (congrArg (fun K : Subgroup G => K ⊓ normalizer (W : Set G)) hHnorm)
    hp ((P.isPGroup'.map E.subtype).map H.subtype) hBX (le_inf hWH W.le_normalizer)
  refine ⟨P, X, B', ?_, hX, hstar, hmax, hfamily⟩
  have hWV : W.subgroupOf H = V := by
    exact comap_map_eq_self_of_injective H.subtype_injective V
  change H ⊓ normalizer (W : Set G) = (normalizer (V : Set H)).map H.subtype
  rw [← hWV, ← subgroupOf_normalizer_eq hWH, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
