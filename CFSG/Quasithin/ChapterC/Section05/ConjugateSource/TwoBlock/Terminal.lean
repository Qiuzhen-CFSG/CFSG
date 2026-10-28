module
public import Theory.GroupTheory.PCoreCommutingProduct
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingNormalizerAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Maximum
/-!
# The full two-block alternating core and centralizer

The full normalizer action first gives C_R(U)=U C_R(K) and its conjugate
counterpart, with K=K₁K₂ and U=U₁U₂. Their Frattini subgroups agree and
are invariant under the chosen outside conjugator. The original common-normal
hypothesis forces them to vanish. The already proved maximum elementary
subgroup C_S(U) then equals C_R(U), so C_R(K)=C_S(K). Finally the genuine
involution in each block kills its central two-cover kernel, and the internal
direct product identifies O₂(K) with U.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

private theorem centralizer_join (A B : Subgroup G) :
    centralizer (A ⊔ B : Subgroup G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

private theorem product_intersection (A B D E : Subgroup G)
    (hDA : D ≤ normalizer (A : Set G)) (hEB : E ≤ normalizer (B : Set G))
    (hAE : A ≤ E) (hBD : B ≤ D) :
    (A ⊔ D) ⊓ (B ⊔ E) = (A ⊔ B) ⊔ (D ⊓ E) := by
  apply le_antisymm
  · rintro g ⟨hg1, hg2⟩
    have hgm : g ∈ (A : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A D hDA]
      exact hg1
    obtain ⟨a, ha, d, hd, rfl⟩ := hgm
    have hdBE : d ∈ B ⊔ E := by
      simpa using (B ⊔ E).mul_mem ((B ⊔ E).inv_mem ((show E ≤ B ⊔ E from le_sup_right) (hAE ha))) hg2
    have hdm : d ∈ (B : Set G) * (E : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left B E hEB]
      exact hdBE
    obtain ⟨b, hb, e, he, rfl⟩ := hdm
    have heD : e ∈ D := by simpa using D.mul_mem (D.inv_mem (hBD hb)) hd
    have hh := mul_mem_sup (mul_mem_sup ha hb) (show e ∈ D ⊓ E from ⟨heD, he⟩)
    simpa only [mul_assoc] using hh
  · apply sup_le
    · exact sup_le (le_inf le_sup_left (hAE.trans le_sup_right))
        (le_inf (hBD.trans le_sup_right) le_sup_left)
    · exact le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right)


private theorem disjoint_three (A B D : Subgroup G) (hA : Disjoint A (B ⊔ D))
    (hB : Disjoint B D) (hc : A ≤ centralizer (B : Set G)) : Disjoint (A ⊔ B) D := by
  rw [disjoint_iff_inf_le]
  rintro g ⟨hg,hgD⟩
  have hm : g ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B ((le_centralizer_iff.mp hc).trans
      (Subgroup.centralizer_le_normalizer _))]
    exact hg
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  have haBD : a ∈ B ⊔ D := by
    have hh := (B ⊔ D).mul_mem (mem_sup_right hgD) ((B ⊔ D).inv_mem (mem_sup_left hb))
    simpa only [mul_inv_cancel_right] using hh
  have ha1 : a = 1 := (show a ∈ (⊥ : Subgroup G) from hA.eq_bot ▸ ⟨ha,haBD⟩)
  have hbD : b ∈ D := by
    change a*b∈D at hgD
    simpa only [ha1,one_mul] using hgD
  have hb1 : b = 1 := (show b ∈ (⊥ : Subgroup G) from hB.eq_bot ▸ ⟨hb,hbD⟩)
  change a*b=1
  simp only [ha1,hb1,mul_one]

private theorem reverse_block_pair {M T K L : Subgroup G}
    (hp : ∀ g ∈ T, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T ∧ K.conjBy (t : G) = L) :
    (∀ g ∈ T, L.conjBy g = L ∨ L.conjBy g = K) ∧
      ∃ t : M, (t : G) ∈ T ∧ L.conjBy (t : G) = K := by
  obtain ⟨t,ht,he⟩ := ht
  constructor
  · intro g hg
    have hh := hp (g*(t:G)) (T.mul_mem hg ht)
    rw [Subgroup.conjBy_mul,he] at hh
    exact hh.symm
  · refine ⟨t⁻¹,T.inv_mem ht,?_⟩
    rw [← he]
    exact Subgroup.conjBy_inv _ _

variable [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.two_block_full_centralizer_product
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (hRM : R ≤ M) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let C := R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    R ⊓ centralizer (U : Set G) = U ⊔ C ∧
      C ≤ centralizer (V : Set G) ∧
      R ⊓ centralizer (V : Set G) = V ⊔ C := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let F₁ := U₁ ⊔ V₁
  let F₂ := U₂ ⊔ V₂
  let U := U₁ ⊔ U₂
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  let C₁ := R ⊓ centralizer (K : Set G)
  let C₂ := R ⊓ centralizer (L : Set G)
  let C := R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let P := R ⊓ centralizer (U : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx hxR hindex hpair ht hnc
  obtain ⟨hp',ht'⟩ := reverse_block_pair hpair ht
  have h1 := h.full_module_centralizer x hxR hnc
  have h2 := h'.full_module_centralizer x hxR hi.second_noncommuting
  have hU₁C₂ : U₁ ≤ C₂ := le_inf (h.module_le.trans inf_le_left) ((map_subtype_le _).trans h'.commute)
  have hU₂C₁ : U₂ ≤ C₁ := le_inf (h'.module_le.trans inf_le_left) ((map_subtype_le _).trans h.commute)
  have hC₁U₁ : C₁ ≤ centralizer (U₁ : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hC₂U₂ : C₂ ≤ centralizer (U₂ : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hCeq : C = C₁ ⊓ C₂ := by
    dsimp only [C,C₁,C₂]
    rw [centralizer_join]
    simp only [inf_assoc,inf_left_comm,inf_left_idem]
  have hprod : P = U ⊔ C := by
    have hiP : P = (R ⊓ centralizer (U₁ : Set G)) ⊓ (R ⊓ centralizer (U₂ : Set G)) := by
      dsimp only [P,U]
      rw [centralizer_join]
      simp only [inf_assoc,inf_left_comm,inf_left_idem]
    rw [hiP,h1,h2,product_intersection U₁ U₂ C₁ C₂
      (hC₁U₁.trans (Subgroup.centralizer_le_normalizer _))
      (hC₂U₂.trans (Subgroup.centralizer_le_normalizer _)) hU₁C₂ hU₂C₁,← hCeq]
  have hCV : C ≤ centralizer (V : Set G) := by
    change C ≤ centralizer ((U₁ ⊔ U₂).map e.toMonoidHom : Set G)
    rw [Subgroup.map_sup,centralizer_join,hCeq]
    exact le_inf (inf_le_left.trans (h.two_block_full_centralizer_centralizes h' M T_H hRM x hx hxR hindex hpair ht hnc))
      (inf_le_right.trans (h'.two_block_full_centralizer_centralizes h M T_H hRM x hx hxR hindex hp' ht' hi.second_noncommuting))
  have hd := h.two_block_direct_product h' M T_H x hx hxR hindex hpair ht hnc
  have hdisj : Disjoint (F₁ ⊔ F₂) D := disjoint_three F₁ F₂ D hd.2.1 hd.2.2.2.1
    (hd.2.2.1.trans (centralizer_le (show F₂ ≤ F₂ ⊔ D from le_sup_left)))
  have hFS : F₁ ⊔ F₂ ≤ S :=
    (sup_le le_sup_left (le_sup_left.trans le_sup_right)).trans_eq hd.1.symm
  have hFC : Disjoint (F₁ ⊔ F₂) C := by
    rw [disjoint_iff_inf_le]
    rintro a ⟨ha,hc⟩
    exact hdisj.le_bot ⟨ha,⟨hFS ha,hc.2⟩⟩
  have hUF : U ≤ F₁ ⊔ F₂ := sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right)
  have hVF : V ≤ F₁ ⊔ F₂ := by
    change (U₁ ⊔ U₂).map e.toMonoidHom ≤ F₁ ⊔ F₂
    rw [Subgroup.map_sup]
    exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)
  have hUC : Disjoint U C := hFC.mono_left hUF
  have hVC : Disjoint V C := hFC.mono_left hVF
  have hCU : C ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (sup_le ((map_subtype_le _).trans le_sup_left) ((map_subtype_le _).trans le_sup_right)))
  obtain ⟨eu,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U C hUC (le_centralizer_iff.mp hCU)
  obtain ⟨ev,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V C hVC (le_centralizer_iff.mp hCV)
  have hPc : Nat.card P = Nat.card U * Nat.card C := by
    rw [hprod,← Nat.card_congr eu.toEquiv,Nat.card_prod]
  have hVc : Nat.card (V ⊔ C : Subgroup G) = Nat.card U * Nat.card C := by
    rw [← Nat.card_congr ev.toEquiv,Nat.card_prod]
    change Nat.card (U.map e.toMonoidHom) * Nat.card C = _
    rw [card_map_of_injective e.injective]
  have hRx : R.map e.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (R : Set G)).inv_mem hxR)
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
  have hPc' : Nat.card P' = Nat.card P := by rw [← hPP,card_map_of_injective e.injective]
  have hUR : U ≤ R := sup_le (h.module_le.trans inf_le_left) (h'.module_le.trans inf_le_left)
  have hVR : V ≤ R := (map_mono hUR).trans_eq hRx
  let : IsElementaryAbelian 2 V := by
    let : IsElementaryAbelian 2 U := by
      let : IsElementaryAbelian 2 U₁ := by
        let := h.block.2.1.elementary
        exact IsElementaryAbelian.map K.subtype
      let : IsElementaryAbelian 2 U₂ := by
        let := h'.block.2.1.elementary
        exact IsElementaryAbelian.map L.subtype
      exact IsElementaryAbelian.sup_of_le_centralizer (hU₂C₁.trans hC₁U₁)
    exact IsElementaryAbelian.map e.toMonoidHom
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


theorem AlternatingPairSetup.two_block_full_centralizer_eq
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hRM : R ≤ M) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    R ⊓ centralizer (U : Set G) = S ⊓ centralizer (U : Set G) ∧
      R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G) =
        S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G) := by
  let S := ChapterB.baumann R
  let U := sourceModule K ⊔ sourceModule L
  let e := MulAut.conj x⁻¹
  let V := U.map e.toMonoidHom
  let C := R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let P := R ⊓ centralizer (U : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  let Q := S ⊓ centralizer (U : Set G)
  let F := (frattini C).map C.subtype
  have hp := h.two_block_full_centralizer_product h' M T_H hRM x hx (hMR hx) hindex hpair ht hnc
  have hq := h.two_block_maximum_core h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hU : IsElementaryAbelian 2 U := by
    let : IsElementaryAbelian 2 (sourceModule K) := by
      let := h.block.2.1.elementary
      exact IsElementaryAbelian.map K.subtype
    let : IsElementaryAbelian 2 (sourceModule L) := by
      let := h'.block.2.1.elementary
      exact IsElementaryAbelian.map L.subtype
    exact IsElementaryAbelian.sup_of_le_centralizer
      ((map_subtype_le _).trans (h.commute.trans (centralizer_le (map_subtype_le _))))
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
    have hnC : normalizer ((K ⊔ L : Subgroup G) : Set G) ≤
        normalizer (centralizer ((K ⊔ L : Subgroup G) : Set G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer ((K ⊔ L : Subgroup G) : Set G))).mp inferInstance
    exact (le_inf (hTHM.trans hMR) (hTHKL.trans hnC)).trans inf_normalizer_le_normalizer_inf
  have hTF : T_H ≤ normalizer (F : Set G) :=
    hTC.trans (normalizer_le_normalizer_characteristic_image C (frattini C))
  have hKLF : K ⊔ L ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp (show F ≤ centralizer ((K ⊔ L : Subgroup G) : Set G) from
      (map_subtype_le _).trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hxF : x ∈ normalizer (F : Set G) := by
    have hh : x⁻¹ ∈ normalizer (F : Set G) := mem_normalizer_iff_map_conj_eq.mpr hFx
    simpa only [inv_inv] using (normalizer (F : Set G)).inv_mem hh
  have hF : F = ⊥ := no_common_normal_index_two R H M T_H F
    ((map_subtype_le _).trans inf_le_left) (hH ▸ sup_le hKLF hTF) hTF hno hindex x hx hi.x_outside hxF
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
    exact inf_le_right.trans (centralizer_le (sup_le ((map_subtype_le _).trans le_sup_left)
      ((map_subtype_le _).trans le_sup_right)))
  have hQP : Q ≤ P := inf_le_inf inf_le_left le_rfl
  have hPQ : P = Q := (eq_of_le_of_card_ge hQP (hq.1.2.2 P inf_le_left hPE)).symm
  refine ⟨hPQ,le_antisymm ?_ (inf_le_inf inf_le_left le_rfl)⟩
  have hCQ : C ≤ Q := (show C ≤ P from le_sup_right.trans_eq hp.1.symm).trans_eq hPQ
  exact le_inf (hCQ.trans inf_le_left) inf_le_right
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}
theorem AlternatingPairSetup.disjoint_blocks
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    Disjoint K L := by
  have hd := alternatingModule_disjoint_of_commuting K L h.block h.commute
  rw [disjoint_iff_inf_le]
  rintro a ⟨haK,haL⟩
  have hc : (⟨a,haK⟩ : K) ∈ centralizer (blockU K : Set K) := by
    intro u _
    exact Subtype.ext (h.commute haL u u.property)
  rw [h.block.2.1.centralizer_blockU,h.block_core_eq_module x hx hnc] at hc
  exact hd.le_bot ⟨mem_map_of_mem K.subtype hc,haL⟩

theorem AlternatingPairSetup.two_block_core_eq_module
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    (K ⊔ L).pCoreIn 2 = sourceModule K ⊔ sourceModule L := by
  rw [pCoreIn_sup_of_disjoint_of_commuting 2 K L (h.disjoint_blocks x hxR hnc)
    (le_centralizer_iff.mp h.commute)]
  change (pCore 2 K).map K.subtype ⊔ (pCore 2 L).map L.subtype = _
  rw [h.block_core_eq_module x hxR hnc,h'.block_core_eq_module x hxR
    (h.fourModuleSourceInputs h'.module_le M T_H x hx hxR hindex hpair ht hnc).second_noncommuting]
  rfl
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
