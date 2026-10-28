module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticKernelMiddlePlacement
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticReciprocalFrattini
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes
public import Theory.Representation.BinaryQuinticDisplacement
public import Theory.SpecificGroups.QuinticInvolutionCommutator

/-!
# Reciprocal kernel containment for the full quintic Frattini subgroup

The middle-placement source puts the literal full kernel in the conjugated
quintic endpoint for the selected StrongFull element.  We use the faithful
binary section on that endpoint: a nontrivial image of the Frattini subgroup
would contain an involution, but its displacement is at least two while the
reciprocal hyperplane gives fixed codimension at most one.  The remaining
central line comparison then removes the possible central transvection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

private theorem full_kernel_frattini_reciprocal_kernel
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
    (g : G) (hg : g ∈ sourceResidual M Mc ⊔ (T : Subgroup G))
    (hRstarcard : Nat.card ((conjugateSpanBy (localModule T M) H).map
      (MulAut.conj g).toMonoidHom ⊓ H.pCoreIn 2 : Subgroup G) = 16) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    let Ustar := U.map (MulAut.conj g).toMonoidHom
    let Qstar := Q.map (MulAut.conj g).toMonoidHom
    let Rstar := Ustar ⊓ Q
    (frattini C).map C.subtype ≤ centralizer (Rstar : Set G) →
      (frattini C).map C.subtype ≤ Qstar := by
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
  let P := (frattini C).map C.subtype
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
    have hpC : P ≤ C := map_subtype_le _
    exact hpC.trans ((source_quintic_full_kernel_middle_placement
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
        (map_subtype_le _)
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

/-- The same selected conjugator puts the full Frattini subgroup in the
reciprocal core centralizer. -/
theorem source_quintic_same_conjugator_frattini_kernel
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
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let Ustar := U.map (MulAut.conj g).toMonoidHom
      let Qstar := Q.map (MulAut.conj g).toMonoidHom
      let Cstar := H.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Ustar : Set G)
      let R := U ⊓ Qstar
      let Rstar := Ustar ⊓ Q
      let W := conjugateSpanBy R X
      Ustar ≤ X.pCoreIn 2 ∧ ¬ Ustar ≤ Q ∧
        localModule T M ≤ U ⊓ Ustar ∧
        (T : Subgroup G) ≤ normalizer ((U ⊓ Ustar : Subgroup G) : Set G) ∧
        (Q ⊓ X.pCoreIn 2) ⊔ (Qstar ⊓ X.pCoreIn 2) = X.pCoreIn 2 ∧
        ⁅U ⊓ Ustar,X.pCoreIn 2⁆ = localModule T M ∧ U = ⁅U,H⁆ ∧
        IsElementaryAbelian 2 W ∧ W ≤ Q ⊓ X.pCoreIn 2 ∧
        X ≤ normalizer (W : Set G) ∧ W ⊓ U = R ∧ W ⊓ Ustar = Rstar ∧
        Rstar ≤ W ∧ ⁅Rstar,U⁆ ≠ ⊥ ∧
        Nat.card R = 16 ∧ Nat.card Rstar = 16 ∧ Nat.card W = 32 ∧
        ⁅W,U⁆ = centralInvolutions T ∧ U ⊓ centralizer (W : Set G) = R ∧
        (W ⊓ C).relIndex W = 2 ∧ 2 * Nat.card (W ⊓ C : Subgroup G) = Nat.card W ∧
        W ⊓ C = R ∧ ⁅W,Q⁆ ≤ U ∧
      (frattini C).map C.subtype ≤ Qstar ∧
      (frattini C).map C.subtype ≤ Cstar := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,
      hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard,hWcomm,hUC,
      hindex,hkernelcard,hWCeq,hWQcomm⟩ :=
    source_quintic_second_kernel_span_strong_full
      hG T hempty hM hu hmany hcard e H hH hi
  let Ustar := U.map (MulAut.conj g).toMonoidHom
  let Qstar := Q.map (MulAut.conj g).toMonoidHom
  let P := (frattini C).map C.subtype
  let Rstar := Ustar ⊓ Q
  let W := conjugateSpanBy (U ⊓ Qstar) X
  let J := conjugateSpanBy W H
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hJQ : J ≤ Q := conjugateSpanBy_le (hWQ.trans inf_le_left) hHQ
  have hHJ : H ≤ normalizer (J : Set G) := le_normalizer_conjugateSpanBy _ _
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy
      (localModule T M) H).trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hWnotC : ¬ W ≤ C := by
    intro hWC
    have hbot : ⁅W,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hWC.trans inf_le_right)
    have hZne : (centralInvolutions T : Subgroup G) ≠ ⊥ := by
      intro hz
      have hzcard : Nat.card (centralInvolutions T) = 2 :=
        plane_centralInvolutions_card T M hM.1.2 hcard e
      rw [hz,card_bot] at hzcard
      omega
    exact hZne (hWcomm.symm.trans hbot)
  have hHD : H ≤ normalizer ((J ⊔ C : Subgroup G) : Set G) := by
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hHJ hh),
      mem_normalizer_iff_map_conj_eq.mp (hHC hh)]
  have hJC : J ⊔ C = Q := by
    rcases (source_quintic_full_kernel_interval hG T hempty hM hu hmany hcard e H hH hi).2
      (J ⊔ C) le_sup_right (sup_le hJQ hCQ) hHD with he | he
    · exact (hWnotC ((le_conjugateSpanBy W H).trans (le_sup_left.trans he.le))).elim
    · exact he
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hJcomm : ⁅J,Q⁆ ≤ U := by
    change ⁅conjugateSpanBy W H,Q⁆ ≤ U
    rw [commutator_conjugateSpanBy_of_normalized_right W H Q
      ((hWQ.trans inf_le_left).trans (pCoreIn_le 2 H)) hHQ]
    exact conjugateSpanBy_le hWQcomm (le_normalizer_conjugateSpanBy _ _)
  have hCJ : ⁅C,J⁆ ≤ U := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hCQ).trans hJcomm
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le hCQ
  have hphi : P ≤ centralizer (J : Set G) :=
    frattini_image_le_centralizer_of_elementary_commutator C J U hpC hCJ inf_le_right
  have hphiR : P ≤ centralizer (Rstar : Set G) :=
    hphi.trans (centralizer_le (hRW.trans (le_conjugateSpanBy W H)))
  have hPq := full_kernel_frattini_reciprocal_kernel hG T hempty hM hu hmany hcard e H hH hi g hg
    hRstarcard hphiR
  have hPCstar : P ≤ H.map (MulAut.conj g).toMonoidHom :=
    (map_subtype_le _).trans ((source_quintic_full_kernel_middle_placement
      hG T hempty hM hu hmany hcard e H hH hi).2 g hg)
  have hZstarUorig : (centralInvolutions T).map
      (MulAut.conj g).toMonoidHom ≤ U := by
    have hZV : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
    have hXV : X ≤ normalizer (localModule T M : Set G) := by
      rw [←InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
      exact sup_le (sourceResidual_le M Mc) hM.1.2
    have hmapV : (localModule T M).map (MulAut.conj g).toMonoidHom =
        localModule T M := mem_normalizer_iff_map_conj_eq.mp (hXV hg)
    exact ((map_mono hZV).trans_eq hmapV).trans (le_conjugateSpanBy _ _)
  have hPcentral : P ≤ centralizer (Ustar : Set G) := by
    have hQcomm : ⁅Qstar,Ustar⁆ ≤ (centralInvolutions T).map
        (MulAut.conj g).toMonoidHom := by
      rw [commutator_comm,←map_commutator]
      exact map_mono (source_quintic_core_commutators
        hG T hempty hM hu hmany hcard e H hH hi).2.le
    have hPU : P ≤ C := map_subtype_le _
    have hQXT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow X (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)
    have hUstarH : Ustar ≤ H := hDQ.trans (hQXT.trans hH.1.1.2)
    have hHC : H ≤ normalizer (C : Set G) :=
      (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy
        (localModule T M) H).trans (normalizer_le_normalizer_centralizer U))).trans
        inf_normalizer_le_normalizer_inf
    have hHP : H ≤ normalizer (P : Set G) := hHC.trans
      (normalizer_le_normalizer_characteristic_image C (frattini C))
    have hUN : Ustar ≤ normalizer (P : Set G) := hUstarH.trans hHP
    have hline : ⁅P,Ustar⁆ ≤ (centralInvolutions T).map
        (MulAut.conj g).toMonoidHom :=
      (commutator_mono hPq le_rfl).trans hQcomm
    have hlineP : ⁅P,Ustar⁆ ≤ P := by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp hUN
    have hlineU : ⁅P,Ustar⁆ ≤ U := hline.trans hZstarUorig
    have hcap := (le_inf hlineP hlineU).trans
      (source_quintic_full_kernel_frattini_span_intersection
        hG T hempty hM hu hmany hcard e H hH hi)
    have hdisj : (centralInvolutions T).map
        (MulAut.conj g).toMonoidHom ⊓ centralInvolutions T = ⊥ := by
      have hh := (source_quintic_reciprocal_core_geometry
        hG T hempty hM hu hmany hcard e H hH hi g hg hescape).2.1
      rw [inf_comm] at hh
      exact hh
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [←hdisj]
    exact le_inf hline hcap
  exact ⟨g,hg,hDQ,hescape,hVI,hTI,hprod,hIQ,hUH,hWel,hWQ,hXW,
    hWU,hWUstar,hRW,hmove,hRcard,hRstarcard,hWcard,hWcomm,hUC,
    hindex,hkernelcard,hWCeq,hWQcomm,hPq,le_inf hPCstar hPcentral⟩

end CFSG.Quasithin.Chapter14.Section06
