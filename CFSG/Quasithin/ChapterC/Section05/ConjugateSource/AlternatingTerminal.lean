module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamilyAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.SingleBlockFrattini
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Terminal
/-!
# Full alternating-five source conclusion in the single-block case

The marked full normalizer action makes the original and conjugate module
centralizers supplement one another. The block centralizer therefore fixes
the conjugate module. Their common Frattini subgroup is invariant under both
source overgroups and vanishes by C.5.2; maximum elementary order identifies
the full Sylow centralizer with its Baumann centralizer. The final theorem
assembles C.5.6(7)(ii), retaining precisely the earlier C.5.4.4 core identity.

Source: Aschbacher–Smith, C.5.6(7), printed pp.158–160.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
omit [Finite G] in
private theorem map_centralizer (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro u hu
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e u) (mem_map_of_mem _ hu)

omit [Finite G] in
private theorem centralizer_centralizes_of_mutual
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (_hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hNK : R ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ normalizer (K : Set G))
    (hsecond : R ⊓ centralizer (sourceModule K : Set G) ≤
      sourceModule K ⊔ (R ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G))) :
    R ⊓ centralizer (K : Set G) ≤
      centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let C := R ⊓ centralizer (K : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  have hVR : V ≤ R := (map_mono (h.module_le.trans inf_le_left)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ ChapterB.baumann R := (map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)))
  have hVU : V ≤ normalizer (U : Set G) := hVS.trans
    (h.normalizes.trans (normalizer_le_normalizer_characteristic_image K (blockU K)))
  have hP'U : P' ≤ normalizer (U : Set G) :=
    hNK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hNC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have hVC : V ≤ normalizer (C : Set G) :=
    (le_inf (hVR.trans R.le_normalizer) ((hVS.trans h.normalizes).trans hNC)).trans inf_normalizer_le_normalizer_inf
  have hCU : C ≤ centralizer (U : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hd : Disjoint U C := alternatingModule_disjoint_of_commuting K C h.block inf_le_right
  intro c hc v hv
  have hcP : c ∈ R ⊓ centralizer (U : Set G) := ⟨hc.1,hCU hc⟩
  have hm : c ∈ (U : Set G) * (P' : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U P' hP'U]
    exact hsecond hcP
  obtain ⟨u,hu,t,ht,hut⟩ := hm
  have hcomm : ⁅c,v⁆ = ⁅u,v⁆ := by
    rw [← hut,commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_mul_comm.mpr (ht.2 v hv).symm]
    simp
  have hcommU : ⁅c,v⁆ ∈ U := hcomm ▸
    (le_normalizer_iff_commutator_le_left.mp hVU) (commutator_mem_commutator hu hv)
  have hcommC : ⁅c,v⁆ ∈ C :=
    (le_normalizer_iff_commutator_le_left.mp hVC) (commutator_mem_commutator hc hv)
  have hzero : ⁅c,v⁆ = 1 := (show ⁅c,v⁆ ∈ (⊥ : Subgroup G) from hd.eq_bot ▸ ⟨hcommU,hcommC⟩)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hzero).symm


theorem AlternatingPairSetup.single_block_full_centralizer_centralizes
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hsq : x^2 ∈ normalizer (K : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    R ⊓ centralizer (K : Set G) ≤
      centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  let U := sourceModule K
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  have hNK : R ⊓ centralizer (V : Set G) ≤ normalizer (K : Set G) := inf_le_left.trans hRK
  have hfirst := h.conjugate_centralizer_le x hx hnc hNK
  apply centralizer_centralizes_of_mutual h x hx hnc hNK
  have hRx : R.map e.toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
  have hUx2 : U.map (MulAut.conj (x^2)).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image K (blockU K) hsq)
  have hVx : V.map e.toMonoidHom = U := by
    change (U.map e.toMonoidHom).map e.toMonoidHom = U
    rw [map_map]
    have he : e.toMonoidHom.comp e.toMonoidHom = (MulAut.conj ((x^2)⁻¹)).toMonoidHom := by
      ext u
      simp [e,pow_two,mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (U : Set G)).inv_mem (mem_normalizer_iff_map_conj_eq.mpr hUx2))
  have hm := map_mono (f := e.toMonoidHom) hfirst
  change (R ⊓ centralizer (V : Set G)).map e.toMonoidHom ≤
    (V ⊔ (R ⊓ centralizer (U : Set G))).map e.toMonoidHom at hm
  rw [Subgroup.map_sup,map_inf _ _ _ e.injective,map_inf _ _ _ e.injective,
    hRx,map_centralizer,map_centralizer,hVx] at hm
  exact hm

theorem AlternatingPairSetup.single_block_full_centralizer_product
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hsq : x^2 ∈ normalizer (K : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let C := R ⊓ centralizer (K : Set G)
    R ⊓ centralizer (U : Set G) = U ⊔ C ∧
      C ≤ centralizer (V : Set G) ∧
      R ⊓ centralizer (V : Set G) = V ⊔ C := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  let F := U ⊔ V
  let C := R ⊓ centralizer (K : Set G)
  let D := S ⊓ centralizer (K : Set G)
  let P := R ⊓ centralizer (U : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  have hprod : P = U ⊔ C := h.full_module_centralizer x hx hnc
  have hCV : C ≤ centralizer (V : Set G) := h.single_block_full_centralizer_centralizes hRK x hx hsq hnc
  have hd := h.conjugate_factor_product x hx hnc
  have hFS : F ≤ S := le_sup_left.trans_eq hd.1.symm
  have hFC : Disjoint F C := by
    rw [disjoint_iff_inf_le]
    rintro a ⟨ha,hc⟩
    exact hd.2.1.le_bot ⟨ha,⟨hFS ha,hc.2⟩⟩
  have hUC : Disjoint U C := hFC.mono_left le_sup_left
  have hVC : Disjoint V C := hFC.mono_left le_sup_right
  have hCU : C ≤ centralizer (U : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  obtain ⟨eu,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U C hUC (le_centralizer_iff.mp hCU)
  obtain ⟨ev,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V C hVC (le_centralizer_iff.mp hCV)
  have hPc : Nat.card P = Nat.card U * Nat.card C := by
    rw [hprod,← Nat.card_congr eu.toEquiv,Nat.card_prod]
  have hVc : Nat.card (V ⊔ C : Subgroup G) = Nat.card U * Nat.card C := by
    rw [← Nat.card_congr ev.toEquiv,Nat.card_prod]
    change Nat.card (U.map e.toMonoidHom) * Nat.card C = _
    rw [card_map_of_injective e.injective]
  have hRx : R.map e.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (R : Set G)).inv_mem hx)
  have hPP : P.map e.toMonoidHom = P' := by
    change (R ⊓ centralizer (U : Set G)).map e.toMonoidHom = R ⊓ centralizer (V : Set G)
    rw [map_inf _ _ _ e.injective,hRx,map_centralizer]
  have hPc' : Nat.card P' = Nat.card P := by rw [← hPP,card_map_of_injective e.injective]
  have hVR : V ≤ R := (map_mono (h.module_le.trans inf_le_left)).trans_eq hRx
  let : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.toMonoidHom
  refine ⟨hprod,hCV,?_⟩
  apply Eq.symm
  apply eq_of_le_of_card_ge (sup_le (le_inf hVR (le_centralizer V)) (le_inf inf_le_left hCV))
  exact (hPc'.trans (hPc.trans hVc.symm)).le
omit [Finite G] in
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

omit [Finite G] in
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


theorem AlternatingPairSetup.single_block_full_centralizer_eq
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G))
    (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    R ⊓ centralizer (U : Set G) = S ⊓ centralizer (U : Set G) ∧
      R ⊓ centralizer (K : Set G) =
        S ⊓ centralizer (K : Set G) := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  let C := R ⊓ centralizer (K : Set G)
  let P := R ⊓ centralizer (U : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  let Q := S ⊓ centralizer (U : Set G)
  let F := (frattini C).map C.subtype
  have hsq : x^2 ∈ normalizer (K : Set G) :=
    hTHK (show x^2 ∈ T_H from (T_H.subgroupOf M).sq_mem_of_index_two hindex (⟨x,hx⟩ : M))
  have hp := h.single_block_full_centralizer_product hRK x (hMR hx) hsq hnc
  obtain ⟨B₀,B₁,hfam,_,_⟩ := h.family_of_index_two H M T_H hTHM hMR hTHK hH hno hindex x hx hnc
  have hq : Q ∈ Stellmacher.elementaryAbelianMaxSubgroups R := by
    change S ⊓ centralizer (U : Set G) ∈ _
    rw [← h.core,hfam]
    exact Set.mem_insert _ _
  have hU : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  have hxout : x ∉ T_H := by
    intro hxt
    have hxU : x ∈ normalizer (U : Set G) :=
      normalizer_le_normalizer_characteristic_image K (blockU K) (hTHK hxt)
    have he : V = U := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (U : Set G)).inv_mem hxU)
    apply hnc
    change V ≤ centralizer (U : Set G)
    rw [he]
    let := hU
    exact le_centralizer U
  have hV : IsElementaryAbelian 2 V := by
    let := hU
    exact IsElementaryAbelian.map e.toMonoidHom
  have hPF : (frattini P).map P.subtype = F :=
    frattini_map_eq_of_central_elementary_supplement P C U
      (h.twoGroup.to_le inf_le_left) hU (le_centralizer_iff.mp inf_le_right) hp.1
  have hP'F : (frattini P').map P'.subtype = F :=
    frattini_map_eq_of_central_elementary_supplement P' C V
      (h.twoGroup.to_le inf_le_left) hV (le_centralizer_iff.mp inf_le_right) hp.2.2
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
  have hTC : T_H ≤ normalizer (C : Set G) := by
    have hnC : normalizer (K : Set G) ≤
        normalizer (centralizer (K : Set G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
    exact (le_inf (hTHM.trans hMR) (hTHK.trans hnC)).trans inf_normalizer_le_normalizer_inf
  have hTF : T_H ≤ normalizer (F : Set G) :=
    hTC.trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hKLF : K ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp (show F ≤ centralizer (K : Set G) from
      (map_subtype_le _).trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hxF : x ∈ normalizer (F : Set G) := by
    have hh : x⁻¹ ∈ normalizer (F : Set G) := mem_normalizer_iff_map_conj_eq.mpr hFx
    simpa only [inv_inv] using (normalizer (F : Set G)).inv_mem hh
  have hF : F = ⊥ := no_common_normal_index_two R H M T_H F
    ((map_subtype_le _).trans inf_le_left) (hH ▸ sup_le hKLF hTF) hTF hno hindex x hx hxout hxF
  have hC : IsElementaryAbelian 2 C := by
    let : Fact (IsPGroup 2 C) := ⟨h.twoGroup.to_le inf_le_left⟩
    apply (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    exact (map_injective C.subtype_injective) (hF.trans (map_bot C.subtype).symm)
  have hPE : IsElementaryAbelian 2 P := by
    let := hU
    let := hC
    have hh : P = U ⊔ C := hp.1
    rw [hh]
    apply IsElementaryAbelian.sup_of_le_centralizer
    exact inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hQP : Q ≤ P := inf_le_inf inf_le_left le_rfl
  have hPQ : P = Q := (eq_of_le_of_card_ge hQP (hq.2.2 P inf_le_left hPE)).symm
  refine ⟨hPQ,le_antisymm ?_ (inf_le_inf inf_le_left le_rfl)⟩
  have hCQ : C ≤ Q := (show C ≤ P from le_sup_right.trans_eq hp.1.symm).trans_eq hPQ
  exact le_inf (hCQ.trans inf_le_left) inf_le_right

open Stellmacher

theorem AlternatingPairSetup.source_C56_single_block_7
    (h : AlternatingPairSetup R K L) (hRK : R ≤ normalizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHK : T_H ≤ normalizer (K : Set G)) (hH : H = K ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (hfull : R ⊓ centralizer (sourceModule K : Set G) = (K ⊔ R).pCoreIn 2)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    K.pCoreIn 2 = U ∧
      (frattini D).map D.subtype = ⊥ ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
      D = R ⊓ centralizer (K : Set G) ∧
      (K ⊔ R).pCoreIn 2 = U ⊔ D ∧
      (K ⊔ R).pCoreIn 2 ∈ elementaryAbelianMaxSubgroups R ∧
      S = (U ⊔ V) ⊔ D ∧ S = elementaryAbelianMaxJ R ∧
      ∃ A : Subgroup G, ∃ r : G,
        r ∈ R ⊓ K ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
        elementaryAbelianMaxSubgroups R =
          {Q, Q.map (MulAut.conj x⁻¹).toMonoidHom, A, A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := (K ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (K : Set G)
  have ht := h.single_block_full_centralizer_eq hRK H M T_H hTHM hMR hTHK hH hno x hx hindex hnc
  have hcore : K.pCoreIn 2 = U := by
    change (pCore 2 K).map K.subtype = _
    rw [h.block_core_eq_module x (hMR hx) hnc]
    rfl
  have hphi := h.frattini_eq_bot_of_index_two H M T_H hTHM hMR hTHK hH hno hindex x hx hnc
  have hprod : (K ⊔ R).pCoreIn 2 = Q := hfull.symm.trans (ht.1.trans h.core.symm)
  have hf := h.single_block_family hRK x (hMR hx) hnc hphi
  have hq : Q ∈ elementaryAbelianMaxSubgroups R := by
    obtain ⟨A,r,_,_,_,he⟩ := hf
    rw [he]
    exact Set.mem_insert _ _
  have hTD : T_H ≤ normalizer (D : Set G) := by
    have hnC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
    exact (le_inf ((hTHM.trans hMR).trans (Stellmacher.normalizer_le_normalizer_baumann R))
      (hTHK.trans hnC)).trans inf_normalizer_le_normalizer_inf
  have hxout : x ∉ T_H := by
    intro hxt
    have hxU : x ∈ normalizer (U : Set G) :=
      normalizer_le_normalizer_characteristic_image K (blockU K) (hTHK hxt)
    have he : V = U := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (U : Set G)).inv_mem hxU)
    apply hnc
    change V ≤ centralizer (U : Set G)
    rw [he]
    let : IsElementaryAbelian 2 U := by
      let := h.block.2.1.elementary
      exact IsElementaryAbelian.map K.subtype
    exact le_centralizer U
  let I := D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom
  have hMI : M ≤ normalizer (I : Set G) :=
    index_two_conjugate_intersection_normalized M T_H D hTHM hindex hTD x hx hxout
  have hKI : K ≤ normalizer (I : Set G) :=
    (le_centralizer_iff.mp (show I ≤ centralizer (K : Set G) from
      inf_le_left.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hI : I = ⊥ := hno I (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (hH ▸ sup_le hKI (hTHM.trans hMI)) hMI
  refine ⟨hcore,hphi,hI,ht.2.symm,hprod.trans h.product,?_,?_,h.baumann_eq_maxJ x (hMR hx) hnc hphi,hf⟩
  · rw [hprod]
    exact hq
  · have hs : S = V ⊔ Q := h.first_factorization x (hMR hx) hnc
    have hq : Q = U ⊔ D := h.product
    change S = (U ⊔ V) ⊔ D
    rw [hs,hq]
    ac_rfl
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
