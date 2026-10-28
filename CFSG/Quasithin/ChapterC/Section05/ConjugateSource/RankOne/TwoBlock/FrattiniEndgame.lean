module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Maximum

/-!
# The common Frattini endgame on the original centralizers

The two full centralizer products have identical Frattini subgroups. Literal
conjugation makes this subgroup x-invariant; the common-normal obstruction
kills it. The full centralizer is then elementary and contains the already
maximum elementary C_S(U), forcing equality and placing C_R(K) inside S.
No disjointness of U and C_R(K) is required.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G]
private theorem map_frattini_equiv (B : Subgroup G) (e : G ≃* G) :
    ((frattini B).map B.subtype).map e.toMonoidHom =
      (frattini (B.map e.toMonoidHom)).map (B.map e.toMonoidHom).subtype := by
  let f := e.subgroupMap B
  have hf : (frattini B).map f.toMonoidHom = frattini (B.map e.toMonoidHom) :=
    f.mapSubgroup.map_radical
  apply le_antisymm
  · rintro g ⟨b, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨f d, hf ▸ mem_map_of_mem f.toMonoidHom hd, ?_⟩
    exact MulEquiv.coe_subgroupMap_apply e B d
  · rintro g ⟨b, hb, rfl⟩
    obtain ⟨d, hd, hdb⟩ := (show b ∈ (frattini B).map f.toMonoidHom from hf.symm ▸ hb)
    refine ⟨(d : G), mem_map_of_mem B.subtype hd, ?_⟩
    exact (MulEquiv.coe_subgroupMap_apply e B d).symm.trans (congrArg Subtype.val hdb)

private theorem no_common_normal_index_two
    (R H M T P : Subgroup G) (hPM : P ≤ R)
    (hHP : H ≤ normalizer (P : Set G)) (hTP : T ≤ normalizer (P : Set G))
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (hindex : T.relIndex M = 2) (x : G) (hx : x ∈ M) (hxT : x ∉ T)
    (hxP : x ∈ normalizer (P : Set G)) : P = ⊥ := by
  apply hno P hPM hHP
  intro g hg
  by_cases hgT : g ∈ T
  · exact hTP hgT
  · have hm : g * x⁻¹ ∈ T := by
      have hi : (T.subgroupOf M).index = 2 := hindex
      exact (mul_mem_iff_of_index_two hi (a := (⟨g, hg⟩ : M))
        (b := (⟨x⁻¹, M.inv_mem hx⟩ : M))).mpr
        (iff_of_false hgT (fun hi => hxT (by
          have hi' : x⁻¹ ∈ T := hi
          simpa only [inv_inv] using T.inv_mem hi')))
    have hh := (normalizer (P : Set G)).mul_mem (hTP hm) hxP
    simpa using hh



variable [Finite G]

theorem centralizer_eq_of_mutual_products
    (R S K U : Subgroup G) (hR : IsPGroup 2 R) (hSR : S ≤ R)
    (hUK : U ≤ K) (hU : IsElementaryAbelian 2 U)
    (H M T : Subgroup G) (hTM : T ≤ M) (hMR : M ≤ normalizer (R : Set G))
    (hTK : T ≤ normalizer (K : Set G)) (hH : H = K ⊔ T)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) → M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T.relIndex M = 2) (hxout : x ∉ T)
    (hprod : R ⊓ centralizer (U : Set G) = U ⊔ (R ⊓ centralizer (K : Set G)))
    (hprod' : R ⊓ centralizer (U.map (MulAut.conj x⁻¹).toMonoidHom : Set G) =
      U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ (R ⊓ centralizer (K : Set G)))
    (hq : S ⊓ centralizer (U : Set G) ∈ Stellmacher.elementaryAbelianMaxSubgroups R) :
    R ⊓ centralizer (U : Set G) = S ⊓ centralizer (U : Set G) ∧
      R ⊓ centralizer (K : Set G) = S ⊓ centralizer (K : Set G) := by
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  let C := R ⊓ centralizer (K : Set G)
  let P := R ⊓ centralizer (U : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  let Q := S ⊓ centralizer (U : Set G)
  let F := (frattini C).map C.subtype
  have hV : IsElementaryAbelian 2 V := by
    let := hU
    exact IsElementaryAbelian.map e.toMonoidHom
  have hPF : (frattini P).map P.subtype = F :=
    frattini_map_eq_of_central_elementary_supplement P C U
      (hR.to_le inf_le_left) hU (le_centralizer_iff.mp inf_le_right) hprod
  have hP'F : (frattini P').map P'.subtype = F :=
    frattini_map_eq_of_central_elementary_supplement P' C V
      (hR.to_le inf_le_left) hV (le_centralizer_iff.mp inf_le_right) hprod'
  have hRx : R.map e.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (R : Set G)).inv_mem (hMR hx))
  have hPP : P.map e.toMonoidHom = P' := by
    change (R ⊓ centralizer (U : Set G)).map e.toMonoidHom = R ⊓ centralizer (V : Set G)
    rw [map_inf _ _ _ e.injective,hRx]
    congr 1
    apply le_antisymm
    · exact map_centralizer_le_centralizer_image _ _
    · intro a ha
      refine ⟨e.symm a,?_,e.apply_symm_apply a⟩
      intro u hu
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using ha (e u) (mem_map_of_mem _ hu)
  have hFx : F.map e.toMonoidHom = F := by
    rw [← hPF,map_frattini_equiv,hPP,hP'F,hPF]
  have hTC : T ≤ normalizer (C : Set G) := by
    have hnC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
    exact (le_inf (hTM.trans hMR) (hTK.trans hnC)).trans inf_normalizer_le_normalizer_inf
  have hTF : T ≤ normalizer (F : Set G) :=
    hTC.trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hKF : K ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp (show F ≤ centralizer (K : Set G) from
      (map_subtype_le _).trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hxF : x ∈ normalizer (F : Set G) := by
    have hh : x⁻¹ ∈ normalizer (F : Set G) := mem_normalizer_iff_map_conj_eq.mpr hFx
    simpa only [inv_inv] using (normalizer (F : Set G)).inv_mem hh
  have hF : F = ⊥ := no_common_normal_index_two R H M T F
    ((map_subtype_le _).trans inf_le_left) (hH ▸ sup_le hKF hTF) hTF hno hindex x hx hxout hxF
  have hC : IsElementaryAbelian 2 C := by
    let : Fact (IsPGroup 2 C) := ⟨hR.to_le inf_le_left⟩
    apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    exact (map_injective C.subtype_injective) (hF.trans (map_bot C.subtype).symm)
  have hPE : IsElementaryAbelian 2 P := by
    let := hU
    let := hC
    rw [show P = U ⊔ C from hprod]
    exact IsElementaryAbelian.sup_of_le_centralizer (inf_le_right.trans (centralizer_le hUK))
  have hQP : Q ≤ P := inf_le_inf hSR le_rfl
  have hPQ : P = Q := (eq_of_le_of_card_ge hQP (hq.2.2 P inf_le_left hPE)).symm
  refine ⟨hPQ,le_antisymm ?_ (inf_le_inf hSR le_rfl)⟩
  have hCQ : C ≤ Q := (show C ≤ P from le_sup_right.trans_eq hprod.symm).trans_eq hPQ
  exact le_inf (hCQ.trans inf_le_left) inf_le_right
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
