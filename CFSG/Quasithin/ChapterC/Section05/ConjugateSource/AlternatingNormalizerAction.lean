module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingOrbit
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.FourModuleNormalizers
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.ModelMarking
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction
/-!
# Full normalizer action and the conjugate module centralizer

The literal marked A₅ action extends to N_G(K) through the proved S₅
normalizer of the natural module. The pair-swap four-group is self-centralizing
there. The actual four-module action identifies the two module stabilizers,
so their full R-centralizers satisfy the mutual supplement bounds. A
commutator belongs both to U and C_R(K), whose intersection is trivial;
therefore C_R(K) centralizes Uˣ.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/

public section
open Subgroup BinaryPermutation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
theorem AlternatingPairSetup.exists_normalizer_action
    (h : AlternatingPairSetup R K L) :
    ∃ q : normalizer (K : Set G) →* FivePerm,
      q.ker = (centralizer (sourceModule K : Set G)).subgroupOf (normalizer (K : Set G)) ∧
      ∀ s : (K ⊔ ChapterB.baumann R : Subgroup G),
        q (inclusion (sup_le K.le_normalizer h.normalizes) s) = h.action s := by
  let H := normalizer (K : Set G)
  have hn : H ≤ normalizer (sourceModule K : Set G) :=
    normalizer_le_normalizer_characteristic_image K (blockU K)
  let e := h.coordinates.trans (coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative
  let ρ := transportedAction hn e
  let a0 := h.action.comp (inclusion (show K ≤ K ⊔ ChapterB.baumann R from le_sup_left))
  have hrange : a0.range = alternatingGroup (Fin 5) := by
    calc
      a0.range = (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action := by
        ext p
        constructor
        · rintro ⟨k,rfl⟩
          exact ⟨inclusion le_sup_left k,k.property,rfl⟩
        · rintro ⟨n,hn,rfl⟩
          exact ⟨⟨n,hn⟩,rfl⟩
      _ = alternatingGroup (Fin 5) := h.block_image
  let a : K →* alternatingGroup (Fin 5) := a0.codRestrict _ (fun k => hrange ▸ (show a0 k ∈ a0.range from ⟨k,rfl⟩))
  have ha : Function.Surjective a := by
    intro p
    obtain ⟨k,hk⟩ := (show (p : FivePerm) ∈ a0.range from hrange.symm ▸ p.property)
    exact ⟨k,Subtype.ext hk⟩
  have he (s : (K ⊔ ChapterB.baumann R : Subgroup G)) (u : sourceModule K) :
      (e.symm (naturalMulAction (Fin 5) (h.action s) (e u)) : G) =
        (s : G) * (u : G) * (s : G)⁻¹ := by
    have hh := h.equivariant s u
    let c := coreEquivNatural (Fin 5) (by decide)
    have hi : e.symm (naturalMulAction (Fin 5) (h.action s) (e u)) =
        h.coordinates.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (h.action s) (h.coordinates u).toAdd)) := by
      apply e.injective
      rw [e.apply_symm_apply]
      change Multiplicative.ofAdd (naturalRepresentation (Fin 5) (h.action s)
        (c (h.coordinates u).toAdd)) =
        Multiplicative.ofAdd (c ((h.coordinates (h.coordinates.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (h.action s) (h.coordinates u).toAdd)))).toAdd))
      rw [h.coordinates.apply_symm_apply]
      exact congrArg Multiplicative.ofAdd (coreEquivNatural_equivariant (Fin 5) (by decide) _ _).symm
    exact (congrArg Subtype.val hi).trans hh
  have himage : (K.subgroupOf H).map ρ =
      (alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) :=
    transportedAction_block_image hn K.le_normalizer a ha e (fun k u => he (inclusion le_sup_left k) u)
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hr : ρ.range ≤ normalizer ((K.subgroupOf H).map ρ : Set _) := by
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map] using
      (K.subgroupOf H).le_normalizer_map ρ
  rw [himage] at hr
  have hp (g : H) : ρ g ∈ (naturalMulAction (Fin 5)).range :=
    normalizer_alternatingFive_naturalMulAction_le_range (hr ⟨g,rfl⟩)
  have hj := naturalMulAction_injective_of_odd (Fin 5) (by decide)
  let q : H →* FivePerm :=
    (MonoidHom.ofInjective hj).symm.toMonoidHom.comp (ρ.codRestrict _ hp)
  have hq (g : H) : naturalMulAction (Fin 5) (q g) = ρ g :=
    MonoidHom.apply_ofInjective_symm hj ⟨ρ g,hp g⟩
  refine ⟨q,?_,?_⟩
  · calc
      q.ker = ρ.ker := by
        ext g
        change q g = 1 ↔ ρ g = 1
        rw [← hq,← (naturalMulAction (Fin 5)).map_one,hj.eq_iff]
      _ = (centralizer (sourceModule K : Set G)).subgroupOf H := transportedAction_ker hn e
  · intro s
    apply hj
    rw [hq]
    apply MulEquiv.ext
    intro v
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e ⟨_,_⟩) : G) = _
    rw [e.symm_apply_apply]
    exact (he s (e.symm v)).symm.trans (by rw [e.apply_symm_apply])

theorem AlternatingPairSetup.conjugate_centralizer_le
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hNK : R ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ normalizer (K : Set G)) :
    R ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤
      (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (R ⊓ centralizer (sourceModule K : Set G)) := by
  let N := K ⊔ ChapterB.baumann R
  let V := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
  have hVN : V ≤ N := ((map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)))).trans le_sup_right
  have hVR : V ≤ R := (map_mono (h.module_le.trans inf_le_left)).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx))
  let inc := inclusion (sup_le K.le_normalizer h.normalizes)
  obtain ⟨q,hker,hcompat⟩ := h.exists_normalizer_action
  rintro r ⟨hr,hc⟩
  let r' : normalizer (K : Set G) := ⟨r,hNK ⟨hr,hc⟩⟩
  have hd : q r' ∈ centralizer (ChapterB.Offenders.D 5 : Set FivePerm) := by
    intro p hp
    have hp' : p ∈ (V.subgroupOf N).map h.action := (h.conjugate_action_image x hx hnc).symm ▸ hp
    obtain ⟨v,hv,rfl⟩ := hp'
    have he := hc v hv
    have he' : inc v * r' = r' * inc v := Subtype.ext he
    have hm := congrArg q he'
    have hqc : q (inc v) = h.action v := hcompat v
    simpa only [map_mul,hqc] using hm
  have hd' := ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action.centralizer_D_le hd
  have hqV : q r' ∈ (V.subgroupOf N).map h.action := (h.conjugate_action_image x hx hnc).symm ▸ hd'
  obtain ⟨v,hv,hvmap⟩ := hqV
  have hk : (inc v)⁻¹ * r' ∈ q.ker := by
    change q ((inc v)⁻¹*r') = 1
    rw [map_mul,map_inv,hcompat,hvmap,inv_mul_cancel]
  have hcc : (v : G)⁻¹ * r ∈ centralizer (sourceModule K : Set G) := hker.le hk
  have hr' : (v : G)⁻¹ * r ∈ R := R.mul_mem (R.inv_mem (hVR hv)) hr
  have hm : (v : G) * ((v : G)⁻¹ * r) ∈ V ⊔ (R ⊓ centralizer (sourceModule K : Set G)) := mul_mem_sup hv (show (v : G)⁻¹ * r ∈ R ⊓ centralizer (sourceModule K : Set G) from ⟨hr',hcc⟩)
  simpa only [mul_inv_cancel_left] using hm

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

theorem AlternatingPairSetup.two_block_mutual_centralizers
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (hRM : R ≤ M) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    R ⊓ centralizer (V : Set G) ≤ V ⊔ (R ⊓ centralizer (U : Set G)) ∧
      R ⊓ centralizer (U : Set G) ≤ U ⊔ (R ⊓ centralizer (V : Set G)) := by
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let e := MulAut.conj x⁻¹
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hNK : R ⊓ centralizer (V : Set G) ≤ normalizer (K : Set G) := by
    rintro r ⟨hr,hc⟩
    have hrU : r ∈ normalizer (U : Set G) :=
      (hi.paired_normalizers.ge ⟨hRM hr,(Subgroup.centralizer_le_normalizer _ hc)⟩).2
    exact (h.block_normalizer_eq_module_normalizer.ge ⟨hr,hrU⟩).2
  have hfirst := h.conjugate_centralizer_le x hxR hnc hNK
  refine ⟨hfirst,?_⟩
  have hRx : R.map e.toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hxR)
  have hUx2 : U.map (MulAut.conj (x^2)).toMonoidHom = U :=
    FourModuleOrbit.x_square_fixes_modules hi.toInputs 0
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

theorem AlternatingPairSetup.two_block_full_centralizer_centralizes
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (hRM : R ≤ M) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    R ⊓ centralizer (K : Set G) ≤
      centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hNK : R ⊓ centralizer ((sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ normalizer (K : Set G) := by
    rintro r ⟨hr,hc⟩
    have hrU : r ∈ normalizer (sourceModule K : Set G) :=
      (hi.paired_normalizers.ge ⟨hRM hr,(Subgroup.centralizer_le_normalizer _ hc)⟩).2
    exact (h.block_normalizer_eq_module_normalizer.ge ⟨hr,hrU⟩).2
  exact centralizer_centralizes_of_mutual h x hxR hnc hNK
    (h.two_block_mutual_centralizers h' M T_H hRM x hx hxR hindex hpair ht hnc).2

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
