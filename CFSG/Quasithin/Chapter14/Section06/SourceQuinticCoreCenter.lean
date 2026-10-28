module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualStructure
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticReciprocalFrattiniKernel

/-!
# The center of the original full quintic core

The same reciprocal conjugator traps the full core center in the reciprocal
core and then its span centralizer. The two full kernels have disjoint
Frattini bounds, so their intersection is elementary. This puts the core
center in the original elementary span, whose core fixed subgroup is the
original Sylow central line.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

private theorem subgroup_full_kernel_reciprocal_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (P : Subgroup G)
    (hPC : P ≤ H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G))
    (g : G) (hg : g ∈ sourceResidual M Mc ⊔ (T : Subgroup G))
    (hRstarcard : Nat.card ((conjugateSpanBy (localModule T M) H).map
      (MulAut.conj g).toMonoidHom ⊓ H.pCoreIn 2 : Subgroup G) = 16) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let Ustar := U.map (MulAut.conj g).toMonoidHom
    let Qstar := Q.map (MulAut.conj g).toMonoidHom
    let Rstar := Ustar ⊓ Q
    P ≤ centralizer (Rstar : Set G) → P ≤ Qstar := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let Qstar := Q.map (MulAut.conj g).toMonoidHom
  let Rstar := Ustar ⊓ Q
  let Z := centralInvolutions T
  let Zstar := Z.map (MulAut.conj g).toMonoidHom
  change (P ≤ centralizer (Rstar : Set G)) → P ≤ Qstar
  intro hphiR
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let : IsElementaryAbelian 2 Ustar := IsElementaryAbelian.map _
  have hZstarV : Zstar ≤ localModule T M := by
    have hXV : X ≤ normalizer (localModule T M : Set G) := by
      rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
      exact sup_le (sourceResidual_le M Mc) hM.1.2
    have hZV : Z ≤ localModule T M := le_conjugateSpanBy _ _
    have hmapV : (localModule T M).map (MulAut.conj g).toMonoidHom =
        localModule T M := mem_normalizer_iff_map_conj_eq.mp (hXV hg)
    exact (map_mono hZV).trans_eq hmapV
  have hZstarU : Zstar ≤ Ustar := map_mono
    ((show Z ≤ localModule T M from le_conjugateSpanBy _ _).trans
      (le_conjugateSpanBy _ _))
  have hZstarUorig : Zstar ≤ U := hZstarV.trans (le_conjugateSpanBy _ _)
  have hZstarQ : Zstar ≤ Q := hZstarUorig.trans hUQ
  have hZstarR : Zstar ≤ Rstar := le_inf hZstarU hZstarQ
  have hRindex : Rstar.relIndex Ustar = 2 := by
    have hUcard : Nat.card Ustar = 32 := by
      rw [card_map_of_injective (MulAut.conj g).injective]
      exact (source_quintic_span_card_and_core_radical
        hG T hempty hM hu hmany hcard e H hH hi).1
    have hh := relIndex_mul_card_of_le (show Rstar ≤ Ustar from inf_le_left)
    rw [hUcard,hRstarcard] at hh
    omega
  obtain ⟨hN,α,hαker,hαnot,hα⟩ :=
    source_quintic_faithful_center_layer_action
      hG T hempty hM hu hmany hcard e H hH hi
  let _ := hN
  let cG := (MulAut.conj g).toMonoidHom
  let Hstar := H.map cG
  let eH : H ≃* Hstar := H.equivMapOfInjective cG (MulAut.conj g).injective
  let π : Hstar →* (H ⧸ pCore 2 H) :=
    (QuotientGroup.mk' (pCore 2 H)).comp eH.symm.toMonoidHom
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp eH.symm.surjective
  have hker_comm (a : H) :
      a ∈ pCore 2 H ↔ ∀ u ∈ U, ⁅(a : G),u⁆ ∈ Z := by
    rw [←hαker]
    constructor
    · intro ha u hu
      have hh := hα a ⟨u,hu⟩
      rw [show α a = 1 from ha] at hh
      have hm := QuotientGroup.eq_iff_div_mem.mp hh
      change u / ((a : G) * u * (a : G)⁻¹) ∈ Z at hm
      have hm' := Z.inv_mem hm
      simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv] using hm'
    · intro ha
      apply MulEquiv.ext
      intro w
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
      rw [hα]
      change QuotientGroup.mk' (Z.subgroupOf U) _ =
        QuotientGroup.mk' (Z.subgroupOf U) u
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (a : G) * (u : G) * (a : G)⁻¹ / (u : G) ∈ Z
      simpa only [commutatorElement_def,div_eq_mul_inv] using ha u u.property
  have hk : ∀ a : Hstar, π a = 1 ↔
      ∀ u ∈ Ustar, ⁅(a : G),u⁆ ∈ Zstar := by
    intro a
    obtain ⟨b,rfl⟩ := eH.surjective a
    have hπb : π (eH b) = QuotientGroup.mk' (pCore 2 H) b := by
      simp only [π,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
    rw [hπb,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    constructor
    · intro hb u hu
      obtain ⟨v,hv,rfl⟩ := hu
      have hv' := mem_map_of_mem cG ((hker_comm b).mp hb v hv)
      change cG ⁅(b : G),v⁆ ∈ Zstar at hv'
      rw [map_commutatorElement] at hv'
      exact hv'
    · intro ha
      apply (hker_comm b).mpr
      intro v hv
      have hv' := ha (cG v) (mem_map_of_mem cG hv)
      change ⁅cG (b : G),cG v⁆ ∈ Z.map cG at hv'
      rw [←map_commutatorElement] at hv'
      exact (mem_map_iff_mem (MulAut.conj g).injective).mp hv'
  let : (Zstar.subgroupOf Ustar).Normal := normal_of_isMulCommutative _
  obtain ⟨σ,c,hσ,_⟩ := Representation.BinaryConjugationSection.exists_faithful_quotient_actor
    Hstar Ustar Zstar (map_mono (hUQ.trans (pCoreIn_le 2 H)))
    hZstarU (by
      have hh := map_mono (f := cG) hHU
      rw [map_equiv_normalizer_eq] at hh
      exact hh)
    (by
      have hHZ : H ≤ centralizer (Z : Set G) :=
        (Section02.SolvableAmalgam.source_small_index_hypothesis_F_1_1
          hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2 (Or.inr hi)).2.2.2.2.2.2
      have hh := map_mono (f := cG)
        (hHZ.trans (Subgroup.centralizer_le_normalizer _))
      rw [map_equiv_normalizer_eq] at hh
      exact hh)
    π hπ hk
  have hPHS : P ≤ Hstar := by
    exact hPC.trans ((source_quintic_full_kernel_middle_placement
      hG T hempty hM hu hmany hcard e H hH hi).2 g hg)
  have hPker : P ≤ Qstar := by
    let A := P.subgroupOf Hstar
    let E := A.map π
    have hfixed : fixedCodim σ E ≤ 1 := by
      apply Representation.BinaryConjugationSection.fixedCodim_le_one_of_fixed_index
        Hstar Ustar Zstar P Rstar σ π c inf_le_left hZstarR
      · exact (commutator_eq_bot_iff_le_centralizer.mpr hphiR).le.trans bot_le
      · exact hRindex.le
    have hEbot : E = ⊥ := by
      by_contra hEne
      have hpP : IsPGroup 2 P := ((isPGroup_pCoreIn 2 H).to_le hCQ).to_le
        hPC
      have hpE : IsPGroup 2 E := hpP.comap_subtype.map π
      have hdiv : 2 ∣ Nat.card E := hpE.card_eq_or_dvd.resolve_left
        (fun h => hEne (card_eq_one.mp h))
      obtain ⟨t,horder⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 hdiv
      have ht2 : orderOf (t : H ⧸ pCore 2 H) = 2 :=
        (Subgroup.orderOf_coe t).trans horder
      obtain ⟨x,hx⟩ := Theory.SpecificGroups.exists_order_five_commutator_of_quintic_model
        (Section02.SolvableAmalgam.source_index_five_models
          hG T hempty hM hu hmany hcard e H hH.1 hi) (t : H ⧸ pCore 2 H) ht2
      have hlow := Representation.BinaryOffender.two_le_displacement_of_commutator_order_five
        σ hσ (t : H ⧸ pCore 2 H) x hx
      have hsub : zpowers (t : H ⧸ pCore 2 H) ≤ E :=
        zpowers_le.mpr t.property
      have hfix : fixedSpace σ E ≤ fixedSpace σ (zpowers (t : H ⧸ pCore 2 H)) := by
        intro v hv a
        exact hv ⟨a,hsub a.property⟩
      have hdim := Submodule.finrank_mono hfix
      have hsumE := fixedCodim_add_finrank σ E
      have hsumt := fixedCodim_add_finrank σ (zpowers (t : H ⧸ pCore 2 H))
      rw [fixedCodim_zpowers_eq_displacement_rank] at hsumt
      omega
    have hkerA : A ≤ π.ker := (Subgroup.map_eq_bot_iff A).mp hEbot
    intro p hp
    have hpA : (⟨p,hPHS hp⟩ : Hstar) ∈ A := hp
    have := hkerA hpA
    have hb := (QuotientGroup.eq_one_iff (eH.symm ⟨p,hPHS hp⟩)).mp this
    have hbQ : ((eH.symm ⟨p,hPHS hp⟩ : H) : G) ∈ Q := ⟨_,hb,rfl⟩
    refine ⟨_,hbQ,?_⟩
    exact congrArg Subtype.val (eH.apply_symm_apply ⟨p,hPHS hp⟩)
  exact hPker

/-- In either original quintic branch, the center of the full core is exactly
its original Sylow central line. -/
theorem source_quintic_full_core_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    (center (H.pCoreIn 2)).map (H.pCoreIn 2).subtype = centralInvolutions T := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let P := (center Q).map Q.subtype
  let Z := centralInvolutions T
  obtain ⟨g,hg,hDQ,hescape,_,_,_,_,_,_,_,_,_,_,_,_,_,hRstarcard,_⟩ :=
    source_quintic_second_kernel_span_strong_full hG T hempty hM hu hmany hcard e H hH hi
  let c := (MulAut.conj g).toMonoidHom
  let Ustar := U.map c
  let Qstar := Q.map c
  let Zstar := Z.map c
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hUQ : U ≤ Q := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1.ge.trans (commutator_le_self Q)
  have hPQ : P ≤ Q := map_subtype_le _
  have hPcentralQ : P ≤ centralizer (Q : Set G) := by
    rintro p ⟨x,hx,rfl⟩ q hq
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨q,hq⟩)
  have hPC : P ≤ C := le_inf (hPQ.trans (pCoreIn_le 2 H))
    (hPcentralQ.trans (centralizer_le hUQ))
  have hPq : P ≤ Qstar := subgroup_full_kernel_reciprocal_core
    hG T hempty hM hu hmany hcard e H hH hi P hPC g hg hRstarcard
    (hPcentralQ.trans (centralizer_le inf_le_right))
  have hPHS : P ≤ H.map c := hPC.trans
    ((source_quintic_full_kernel_middle_placement
      hG T hempty hM hu hmany hcard e H hH hi).2 g hg)
  have hZstarU : Zstar ≤ U := by
    have hZV : Z ≤ localModule T M := le_conjugateSpanBy _ _
    have hXV : X ≤ normalizer (localModule T M : Set G) := by
      rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
      exact sup_le (sourceResidual_le M Mc) hM.1.2
    have hmapV : (localModule T M).map c = localModule T M :=
      mem_normalizer_iff_map_conj_eq.mp (hXV hg)
    exact ((map_mono hZV).trans_eq hmapV).trans (le_conjugateSpanBy _ _)
  have hPU : P ⊓ U ≤ Z :=
    (le_inf inf_le_right (inf_le_left.trans hPcentralQ)).trans
      (source_quintic_span_card_and_core_radical
        hG T hempty hM hu hmany hcard e H hH hi).2.le
  have hdisj : Zstar ⊓ Z = ⊥ := by
    have hh := (source_quintic_reciprocal_core_geometry
      hG T hempty hM hu hmany hcard e H hH hi g hg hescape).2.1
    rw [inf_comm] at hh
    exact hh
  have hPcentral : P ≤ centralizer (Ustar : Set G) := by
    have hQcomm : ⁅Qstar,Ustar⁆ ≤ Zstar := by
      rw [commutator_comm,←map_commutator]
      exact map_mono (source_quintic_core_commutators
        hG T hempty hM hu hmany hcard e H hH hi).2.le
    have hQXT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow X (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)
    have hUstarH : Ustar ≤ H := hDQ.trans (hQXT.trans hH.1.1.2)
    have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hHP : H ≤ normalizer (P : Set G) := hHQ.trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
    have hline : ⁅P,Ustar⁆ ≤ Zstar := (commutator_mono hPq le_rfl).trans hQcomm
    have hlineP : ⁅P,Ustar⁆ ≤ P :=
      le_normalizer_iff_commutator_le_left.mp (hUstarH.trans hHP)
    have hcap : ⁅P,Ustar⁆ ≤ Z := (le_inf hlineP (hline.trans hZstarU)).trans hPU
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [←hdisj]
    exact le_inf hline hcap
  have hPCstar : P ≤ C.map c := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hPHS hx
    refine ⟨y,⟨hy,?_⟩,he⟩
    intro u hu
    apply (MulAut.conj g).injective
    change c (u * y) = c (y * u)
    simp only [map_mul]
    rw [he]
    exact hPcentral hx (c u) (mem_map_of_mem c hu)
  let E := C ⊓ C.map c
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le hCQ
  have hPhi : (frattini C).map C.subtype ≤ Z :=
    source_quintic_full_kernel_frattini_le_point hG T hempty hM hu hmany hcard e H hH hi
  let : IsElementaryAbelian 2 E := conjugate_intersection_elementary hpC hPhi g
    (disjoint_iff.mpr (by simpa only [inf_comm] using hdisj))
  have hPE : P ≤ E := le_inf hPC hPCstar
  have hPomega : P ≤ omegaOneAmbient C := by
    intro p hp
    apply (omegaOneAmbient_le_iff C (omegaOneAmbient C)).mp le_rfl p (hPC hp)
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) p (hPE hp)
  have hPU' : P ≤ U := hPomega.trans_eq
    (source_quintic_full_kernel_omega hG T hempty hM hu hmany hcard e H hH hi)
  apply le_antisymm ((le_inf le_rfl hPU').trans hPU)
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  intro z hz
  refine ⟨⟨z,hUQ (hZU hz)⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext ((hHZ ((pCoreIn_le 2 H) q.property)) z hz).symm

/-- The full core centralizer of the actual order-five residual is the
original Sylow central line. -/
theorem source_quintic_large_five_residual_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    H.pCoreIn 2 ⊓ centralizer ((⁅H.pCoreIn 2,A⁆ : Subgroup G) : Set G) =
      centralInvolutions T := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let R := ⁅Q,A⁆
  have hZ := source_quintic_full_core_center hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨_,_,_,_,_,hUR,hRC,_⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  change R ⊔ C = Q at hRC
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  let : IsMulCommutative C := (source_quintic_full_kernel_structure
    hG T hempty hM hu hmany hcard e H hH hi).1
  rw [←hZ]
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ C := ⟨(pCoreIn_le 2 H) hx.1,
      (centralizer_le hUR) hx.2⟩
    have hCx : C ≤ centralizer ({x} : Set G) := by
      intro y hy
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : C) ⟨x,hxC⟩)
    have hQx : Q ≤ centralizer ({x} : Set G) := by
      rw [←hRC]
      exact sup_le (fun r hr => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx.2 r hr)) hCx
    refine ⟨⟨x,hx.1⟩,mem_center_iff.mpr (fun q => ?_),rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hQx q.property))
  · rintro x ⟨q,hq,rfl⟩
    refine ⟨q.property,?_⟩
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp hq ⟨r,hRQ hr⟩)

end CFSG.Quasithin.Chapter14.Section06
