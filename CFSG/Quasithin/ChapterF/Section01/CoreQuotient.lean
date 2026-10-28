module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.AmbientQuotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.QuotientIntersection

/-!
# The literal two-core quotient of a rank-one pair

If S is Sylow in the generated group W, the kernel of W → W/O₂(W)
lies in S. Local Sylow intersections and their normalizers therefore map
onto the corresponding intersections and Borels. Removing a two-group
kernel preserves each quotient Lᵢ/O₂(Lᵢ). The six original F.1.1 clauses
then descend as soon as the two image parabolics have characteristic two.

This is the second weak BN-pair construction in Aschbacher--Smith,
original 15.2.4, printed p.1106. It does not assert the mixed DGS85
exclusion or assume normality of the residual in a larger local group.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- The image of the literal local Borel is the image local Borel. -/
theorem borel_map_of_ker_le (f : G →* H) (L S : Subgroup G)
    (hSyl : Chapter1.IsSylowIn 2 (S ⊓ L) L) (hk : f.ker ≤ S) :
    (borel L S).map f = borel (L.map f) (S.map f) := by
  obtain ⟨P,hP⟩ := hSyl
  let g := f.subgroupMap L
  let Q : Sylow 2 (L.map f) := P.mapSurjective (f := g) (f.subgroupMap_surjective L)
  have hI : (S ⊓ L).map f = S.map f ⊓ L.map f := by
    rw [inf_comm, map_inf_of_ker_le f L S hk, inf_comm]
  have hQ : (Q : Subgroup (L.map f)).map (L.map f).subtype = S.map f ⊓ L.map f := by
    change ((P : Subgroup L).map g).map (L.map f).subtype = _
    rw [map_map]
    change (P : Subgroup L).map (f.comp L.subtype) = _
    rw [←map_map,hP,hI]
  have hn := Sylow.normalizer_map_surjective P g (f.subgroupMap_surjective L)
  have hm := congrArg (Subgroup.map (L.map f).subtype) hn
  have hb := borel_subgroupOf_eq_sylowNormalizer L S P hP
  have hb' := borel_subgroupOf_eq_sylowNormalizer (L.map f) (S.map f) Q hQ
  change ((sylowNormalizer P).map g).map (L.map f).subtype =
    (sylowNormalizer Q).map (L.map f).subtype at hm
  rw [←hb,←hb',map_subgroupOf_eq_of_le (borel_le _ _),map_map] at hm
  change ((borel L S).subgroupOf L).map (f.comp L.subtype) = _ at hm
  rwa [←map_map,map_subgroupOf_eq_of_le (borel_le _ _)] at hm

omit [Finite G] in
private theorem borel_subgroupOf (L S W : Subgroup G) (hL : L ≤ W) :
    borel (L.subgroupOf W) (S.subgroupOf W) = (borel L S).subgroupOf W := by
  unfold borel
  change L.subgroupOf W ⊓ normalizer ((S ⊓ L).subgroupOf W : Set W) = _
  rw [←subgroupOf_normalizer_eq (inf_le_right.trans hL)]
  rfl

private theorem rankOne_model_equiv {A B : Type*} [Group A] [Group B]
    (e : B ≃* A) (h : IsRankOneModel A) : IsRankOneModel B := by
  cases h with
  | linear n hn h =>
    obtain ⟨F,hF,hfin,hcard,⟨d⟩⟩ := h
    exact .linear n hn ⟨F,hF,hfin,hcard,⟨e.trans d⟩⟩
  | suzuki m h => exact .suzuki m ⟨e.trans h.some⟩
  | projective_unitary n hn h =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨d⟩⟩ := h
    exact .projective_unitary n hn ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans d⟩⟩
  | special_unitary n hn h =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨d⟩⟩ := h
    exact .special_unitary n hn ⟨F,hF,hfin,J,hcard,hconj,⟨e.trans d⟩⟩
  | dihedral h => exact .dihedral ⟨e.trans h.some⟩


private noncomputable def localCoreQuotientEquiv [Finite H] (f : G →* H)
    (hk : IsPGroup 2 f.ker) (L : Subgroup G) :
    (L ⧸ pCore 2 L) ≃* (L.map f ⧸ pCore 2 (L.map f)) :=
  (f.subgroupMap L).pCoreQuotientEquiv (f.subgroupMap_surjective L)
    (by rw [ker_subgroupMap]; exact hk.comap_subtype)

private theorem localPair_map [Finite H] (f : G →* H) (L : Fin 2 → Subgroup G)
    (S : Subgroup G) (hkS : f.ker ≤ S) (hk : IsPGroup 2 f.ker)
    (hS : IsPGroup 2 S)
    (hN : ∀ i, S ≤ normalizer (L i : Set G))
    (hSyl : ∀ i, Chapter1.IsSylowIn 2 (S ⊓ L i) (L i))
    (hQ : ∀ i, IsRankOneModel (L i ⧸ pCore 2 (L i)))
    (hX : ∀ i, borel (L (other i)) S ≤ normalizer (L i : Set G))
    (hfree : pCore 2 (generated (fun i => (L i).map f) (S.map f)) = ⊥)
    (hc : ∀ i, generalizedFitting (parabolic (fun i => (L i).map f) (S.map f) i) =
      pCore 2 (parabolic (fun i => (L i).map f) (S.map f) i)) :
    HypothesisF11 (fun i => (L i).map f) (S.map f) := by
  refine ⟨inferInstance,hS.map f,?_,?_,?_,?_,hfree,hc⟩
  · intro i
    exact (map_mono (hN i)).trans ((L i).le_normalizer_map f)
  · intro i
    have hm := Chapter1.Section02.IndexTwo.isSylowIn_map (hSyl i) f
    rwa [inf_comm S, map_inf_of_ker_le f (L i) S hkS, inf_comm] at hm
  · intro i
    exact rankOne_model_equiv (localCoreQuotientEquiv f hk (L i)).symm (hQ i)
  · intro i
    rw [←borel_map_of_ker_le f _ _ (hSyl _) hkS]
    exact (map_mono (hX i)).trans ((L i).le_normalizer_map f)

omit [Finite G] in
private theorem generated_le (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) :
    L i ≤ generated L S := by
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left

/-- The original local rank-one clauses descend through the generated two-core. -/
theorem localPair_coreQuotient (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (hSylW : Chapter1.IsSylowIn 2 S (generated L S))
    (hN : ∀ i, S ≤ normalizer (L i : Set G))
    (hSyl : ∀ i, Chapter1.IsSylowIn 2 (S ⊓ L i) (L i))
    (hQ : ∀ i, IsRankOneModel (L i ⧸ pCore 2 (L i)))
    (hX : ∀ i, borel (L (other i)) S ≤ normalizer (L i : Set G)) :
    let W := generated L S
    let q := QuotientGroup.mk' (pCore 2 W)
    let Lhat := fun i => ((L i).subgroupOf W).map q
    let Shat := (S.subgroupOf W).map q
    (∀ i, generalizedFitting (((parabolic L S i).subgroupOf W).map q) =
      pCore 2 (((parabolic L S i).subgroupOf W).map q)) →
      HypothesisF11 Lhat Shat ∧
      (∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃*
        (Lhat i ⧸ pCore 2 (Lhat i)))) ∧
      (∀ i, borel (Lhat i) Shat = ((borel (L i) S).subgroupOf W).map q) ∧
      (∀ i, parabolic Lhat Shat i = ((parabolic L S i).subgroupOf W).map q) := by
  intro W q Lhat Shat hc
  have hLW (i : Fin 2) : L i ≤ W := generated_le L S i
  have hSW : S ≤ W := le_sup_right
  let A := fun i => (L i).subgroupOf W
  let R := S.subgroupOf W
  obtain ⟨P,hP⟩ := hSylW
  have hRP : R = (P : Subgroup W) := by
    exact (congrArg (fun K : Subgroup G => K.subgroupOf W) hP.symm).trans
      (comap_map_eq_self_of_injective W.subtype_injective _)
  have hkS : q.ker ≤ R := by
    rw [QuotientGroup.ker_mk',hRP]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hAS (i : Fin 2) : Chapter1.IsSylowIn 2 (R ⊓ A i) (A i) := by
    apply (Chapter1.IsSylowIn.map_iff W.subtype W.subtype_injective).mp
    rw [Subgroup.map_inf _ _ _ W.subtype_injective]
    simpa only [A,R,map_subgroupOf_eq_of_le hSW,map_subgroupOf_eq_of_le (hLW i)] using hSyl i
  let e (i : Fin 2) := (subgroupOfEquivOfLe (hLW i)).symm
  let eQ (i : Fin 2) := (e i).toMonoidHom.pCoreQuotientEquiv (p := 2) (e i).surjective
    (IsPGroup.ker_isPGroup_of_injective (e i).injective)
  let d (i : Fin 2) := (eQ i).trans (localCoreQuotientEquiv q hk (A i))
  have hfree : pCore 2 (generated Lhat Shat) = ⊥ := by
    have hg : generated Lhat Shat = ⊤ := by
      change (A 0).map q ⊔ (A 1).map q ⊔ R.map q = ⊤
      rw [←Subgroup.map_sup,←Subgroup.map_sup]
      have ha : A 0 ⊔ A 1 ⊔ R = ⊤ := by
        change (L 0).subgroupOf W ⊔ (L 1).subgroupOf W ⊔ S.subgroupOf W = ⊤
        rw [←subgroupOf_sup (hLW 0) (hLW 1),
          ←subgroupOf_sup (sup_le (hLW 0) (hLW 1)) hSW]
        exact subgroupOf_self W
      rw [ha,←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    have hQfree : pCore 2 (W ⧸ pCore 2 W) = ⊥ := by
      have hh := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk
      have hm := congrArg (Subgroup.map q) hh
      rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),QuotientGroup.map_mk'_self] at hm
      exact hm
    rw [hg]
    have hi := pCore_map_iso 2 (topEquiv : (⊤ : Subgroup (W ⧸ pCore 2 W)) ≃* _)
    rw [hQfree] at hi
    exact (map_eq_bot_iff_of_injective _ topEquiv.injective).mp hi
  have hB (i : Fin 2) : borel (Lhat i) Shat = ((borel (L i) S).subgroupOf W).map q := by
    rw [←borel_map_of_ker_le q (A i) R (hAS i) hkS]
    exact congrArg (Subgroup.map q) (borel_subgroupOf _ _ _ (hLW i))
  have hP (i : Fin 2) : parabolic Lhat Shat i = ((parabolic L S i).subgroupOf W).map q := by
    unfold parabolic
    rw [hB]
    change (A i).map q ⊔ R.map q ⊔ _ = _
    rw [←Subgroup.map_sup,←Subgroup.map_sup]
    congr 1
    exact ((subgroupOf_sup (sup_le (hLW i) hSW)
      ((borel_le _ _).trans (hLW (other i)))).trans
        (congrArg (fun B : Subgroup W => B ⊔ (borel (L (other i)) S).subgroupOf W)
          (subgroupOf_sup (hLW i) hSW))).symm
  refine ⟨?_,fun i => ⟨d i⟩,hB,hP⟩
  · apply localPair_map q A R hkS hk (hRP.symm ▸ P.isPGroup') ?_ hAS ?_ ?_ hfree (fun i => (hP i).symm ▸ hc i)
    · intro i
      change R ≤ normalizer ((L i).subgroupOf W : Set W)
      rw [←subgroupOf_normalizer_eq (hLW i)]
      exact comap_mono (hN i)
    · intro i
      exact rankOne_model_equiv (eQ i).symm (hQ i)
    · intro i
      rw [borel_subgroupOf _ _ _ (hLW (other i)),←subgroupOf_normalizer_eq (hLW i)]
      exact comap_mono (hX i)

end CFSG.Quasithin.ChapterF.Source
