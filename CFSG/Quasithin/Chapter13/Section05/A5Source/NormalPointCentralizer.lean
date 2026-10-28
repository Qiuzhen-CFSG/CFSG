module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalMaximal
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# The original normal A₅ point centralizer and its quaternion core

An element of O₂(H) acts on the quaternion closure U_H by an inner
 automorphism. Correcting it by an element of U_H leaves an element
centralizing the original seed; the proved local core equality then puts
it back in U_H. Thus O₂(H)=U_H. The full point centralizer has the same
core and seed span by F.9 and the common Sylow subgroup.

The literal square action bounds the point-centralizer quotient order by
72. The commuting original cubic and symmetric-three pair make |H/O₂(H)|
divisible by eighteen. Hence H has two-power index in the point centralizer,
while the original Sylow subgroup makes this index odd. This proves H=G₁.
Finally L₁T has index three, giving the full singleton conclusion for H_z.
The last theorem supplies the actual involution centralizer, module
normalizer and local cores used in the F.4.31 application of 13.5.17.

The original A₅ Context and the genuine earlier universal A.3.12 input
are retained. The weak-BN construction and model recognition in 13.5.17
remain separate source obligations.

Source: Aschbacher–Smith, 13.5.15(6),(8) and 13.5.17,
printed pp.920–922 (PDF pp.937–939).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

private theorem normal_core_eq_closure_sup_centralizer :
    Source.QH H = Source.UH H V₃ ⊔
      (Source.QH H ⊓ centralizer (Source.UH H V₃ : Set G)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have h : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨q,hz⟩ := normal_quaternion_with_center d hA312 hH hU hn
  change QuaternionCentralProductData D.UH at q
  change (center D.UH).map D.UH.subtype = D.V₁ at hz
  change D.QH = D.UH ⊔ (D.QH ⊓ centralizer (D.UH : Set G))
  apply le_antisymm ?_ (sup_le h.UH_le_QH inf_le_left)
  intro a ha
  have haH : a ∈ D.H := (pCoreIn_le 2 D.H) ha
  let α := D.UH.normalizerMonoidHom ⟨a,le_normalizer_conjugateSpanBy D.Vplus D.H haH⟩
  have hα : quotientAut (center D.UH) α = 1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center D.UH) v
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (mem_map_iff_mem D.UH.subtype_injective).mp
    rw [hz]
    have hh := (h.mem_kernel_iff h.UH_le_H).mp (h.kernel_UH_eq_QH.symm ▸ ha)
    have hh' : ⁅a,(u:G)⁆ ∈ D.V₁ := by
      rw [←commutatorElement_inv]
      exact D.V₁.inv_mem (hh.2 u u.property)
    rw [map_div, div_eq_mul_inv]
    change (α u : G) * (u : G)⁻¹ ∈ D.V₁
    simpa only [α, normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using hh'
  obtain ⟨u,hu⟩ := (q.quotientAut_eq_one_iff_inner α).mp hα
  have hc : (u:G)⁻¹ * a ∈ centralizer (D.UH : Set G) := by
    intro x hx
    have he := congrArg (fun b : MulAut D.UH => (b ⟨x,hx⟩ : G)) hu
    change (u:G)*x*(u:G)⁻¹ = a*x*a⁻¹ at he
    calc
      x * ((u:G)⁻¹*a) = (u:G)⁻¹*((u:G)*x*(u:G)⁻¹)*a := by group
      _ = (u:G)⁻¹*(a*x*a⁻¹)*a := by rw [he]
      _ = ((u:G)⁻¹*a)*x := by group
  have hp := mul_mem_sup u.property
    (show (u:G)⁻¹*a ∈ D.QH ⊓ centralizer (D.UH : Set G) from
      ⟨D.QH.mul_mem (D.QH.inv_mem (h.UH_le_QH u.property)) ha,hc⟩)
  simpa only [mul_inv_cancel_left] using hp

/-- The original local two-core is exactly the quaternion seed closure. -/
theorem normal_core_eq_closure : Source.QH H = Source.UH H V₃ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have h : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨r,hrH,_,hcore,_,_,_⟩ := source_normal_pair_normal d hA312 hH hU hn
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  have hI : I ≤ H := sup_le h.V_le_H (by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (h.V_le_H hv)) (H.inv_mem hrH))
  have hc : Source.QH H ⊓ centralizer (Source.UH H V₃ : Set G) ≤ V₁ := by
    rw [←normal_pair_centralizer_eq_point d hA312 hH hU hn I hI hcore]
    apply le_inf ?_ inf_le_right
    apply le_trans ?_ (show V ≤ I from le_sup_left)
    rw [←normal_local_core_eq_module d hA312 hH hU hn]
    apply le_trans ?_ (d.local_centralizers d.normalizes_L).2.le
    exact le_inf (inf_le_left.trans (h.QH_le_T.trans le_sup_right))
      (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V₃ H)))
  rw [normal_core_eq_closure_sup_centralizer d hA312 hH hU hn]
  exact sup_eq_left.mpr (hc.trans (h.point_lt.le.trans (le_conjugateSpanBy V₃ H)))

omit hU hn hA312 [IsElementaryAbelian 2 V] in
private theorem point_mem_family :
    centralizer (V₁ : Set G) ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
      (centralizer (V₁ : Set G)) (normalizer (L : Set G)) := by
  let Z := centralizer (V₁ : Set G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hTZ : (T : Subgroup G) ≤ Z := hTH.trans hH.2.1
  have hlineT : V₁ ≤ (T : Subgroup G) :=
    d.flag.one_le_two.trans (d.flag.two_le_V.trans d.chosen.le_sylow)
  have hc : V₁ ≤ Z.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hlineT) (hlineT.trans hTZ) (centralizer_le_normalizer V₁)
  refine ⟨⟨?_,hH.1.2.trans hH.2.1⟩,le_rfl,fun he => hH.2.2 (hH.2.1.trans he)⟩
  intro he
  have hb := bot_unique (hc.trans_eq he)
  have hcard := d.flag.one_card
  rw [hb,card_bot] at hcard
  contradiction

/-- The full original point centralizer has the same quaternion core as H. -/
theorem normal_point_core_eq_closure :
    (centralizer (V₁ : Set G)).pCoreIn 2 = Source.UH H V₃ := by
  let Z := centralizer (V₁ : Set G)
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  let Dz : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,Z⟩
  have h : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hz : Dz.Hypothesis :=
    (source13_5_7 d hA312 (point_mem_family d hH)).f9Hypothesis
  have ht : Z.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow Z (T.subtype hz.T_le_H)).trans_eq
      (map_subgroupOf_eq_of_le hz.T_le_H)
  have hcore : Z.pCoreIn 2 ≤ Source.QH H :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Z) (ht.trans h.T_le_H)
      (h.H_centralizes.trans (Z.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image Z (pCore 2 Z))))
  rw [normal_core_eq_closure d hA312 hH hU hn] at hcore
  exact le_antisymm hcore
    ((conjugateSpanBy_mono le_rfl h.H_centralizes).trans hz.UH_le_QH)

/-- Enlarging H to the original point centralizer leaves its seed span unchanged. -/
theorem normal_point_span_eq_closure :
    Source.UH (centralizer (V₁ : Set G)) V₃ = Source.UH H V₃ := by
  let Z := centralizer (V₁ : Set G)
  let Dz : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,Z⟩
  have hz : Dz.Hypothesis :=
    (source13_5_7 d hA312 (point_mem_family d hH)).f9Hypothesis
  exact le_antisymm
    (hz.UH_le_QH.trans (normal_point_core_eq_closure d hA312 hH hU hn).le)
    (conjugateSpanBy_mono le_rfl hH.2.1)

/-- The actual normal cubic and the symmetric-three pair give the source
quotient an order divisible by eighteen. -/
theorem normal_star_card_multiple_eighteen : 18 ∣ Nat.card (Source.Hstar H) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have h : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨_,_,_,_,r,hrH,_,_,_,⟨j⟩⟩ := source_normal_pair_core d hA312 hH hU hn
  let I := V ⊔ V.map (MulAut.conj r).toMonoidHom
  let π := QuotientGroup.mk' (pCore 2 H)
  let A := Source.starImage H (residualCentralizer L V₁)
  let J := Source.starImage H I
  change J ≃* Equiv.Perm (Fin 3) at j
  let : ((residualCentralizer L V₁).subgroupOf H).Normal := hn
  let : A.Normal := Normal.map hn π (QuotientGroup.mk'_surjective _)
  have hA : Nat.card A = 3 := by
    rw [Nat.card_congr (normal_residual_star_cubic d hA312 hH hU hn).toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have hJ : Nat.card J = 6 := by
    rw [Nat.card_congr j.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hseed : D.Vplus = ⁅D.V,D.L₁⁆ := d.third_eq_commutator
  have hv : Source.starImage H V ≤ centralizer (A : Set (Source.Hstar H)) := by
    rintro _ ⟨v,hv,rfl⟩ _ ⟨l,hl,rfl⟩
    have hc : ⁅v,l⁆ ∈ pCore 2 H := by
      have hm : (⁅v,l⁆ : H).val ∈ D.QH := h.UH_le_QH
        (le_conjugateSpanBy _ _ (hseed.symm ▸ commutator_mem_commutator hv hl))
      exact (show D.QH.subgroupOf H = pCore 2 H from
        comap_map_eq_self_of_injective H.subtype_injective _) ▸ hm
    have he : π v * π l = π l * π v := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hc
    exact he.symm
  have hconj : V.map (MulAut.conj r).toMonoidHom ≤ H := by
    rintro _ ⟨v,hv,rfl⟩
    exact H.mul_mem (H.mul_mem hrH (h.V_le_H hv)) (H.inv_mem hrH)
  have hcent : J ≤ centralizer (A : Set (Source.Hstar H)) := by
    change (I.subgroupOf H).map π ≤ _
    rw [show I = V ⊔ V.map (MulAut.conj r).toMonoidHom from rfl,
      subgroupOf_sup h.V_le_H hconj,Subgroup.map_sup]
    refine sup_le hv ?_
    rintro _ ⟨x,⟨v,hvV,he⟩,rfl⟩
    let rH : H := ⟨r,hrH⟩
    let vH : H := ⟨v,h.V_le_H hvV⟩
    have hx : x = rH*vH*rH⁻¹ := Subtype.ext he.symm
    rw [hx,map_mul,map_mul,map_inv]
    have hnA : π rH ∈ normalizer (A : Set (Source.Hstar H)) := by
      rw [A.normalizer_eq_top]
      trivial
    exact (mem_normalizer_iff.mp ((normalizer_le_normalizer_centralizer A) hnA)
      (π vH)).mp (hv (mem_map_of_mem π hvV))
  have hd : Disjoint A J := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    let xJ : J := ⟨x,hx.2⟩
    have he : j xJ = 1 := by
      have hc : ∀ x : Equiv.Perm (Fin 3), (∀ y, y*x=x*y) → x=1 := by decide +kernel
      apply hc
      intro y
      obtain ⟨y,rfl⟩ := j.surjective y
      rw [←map_mul,←map_mul]
      apply congrArg j
      exact Subtype.ext ((hcent y.property x hx.1).symm)
    have hx1 : xJ=1 := j.injective (he.trans j.map_one.symm)
    exact congrArg Subtype.val hx1
  have hc : Nat.card (A ⊔ J : Subgroup (Source.Hstar H)) = 18 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A J
      (hcent.trans (centralizer_le_normalizer A)) hd,hA,hJ]
  rw [←hc]
  exact (A ⊔ J : Subgroup (Source.Hstar H)).card_subgroup_dvd_card

/-- The quaternion square action and the original Sylow subgroup force H
 to be the full point centralizer, as required in 13.5.15(6) and 13.5.17. -/
theorem normal_eq_point_centralizer : H = centralizer (V₁ : Set G) := by
  let Z := centralizer (V₁ : Set G)
  let Dz : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,Z⟩
  have hz : Dz.Hypothesis :=
    (source13_5_7 d hA312 (point_mem_family d hH)).f9Hypothesis
  have hspan : Source.UH Z V₃ = Source.UH H V₃ :=
    normal_point_span_eq_closure d hA312 hH hU hn
  have hq : ∃ q : QuaternionCentralProductData Dz.UH,
      (center Dz.UH).map Dz.UH.subtype = Dz.V₁ := by
    change ∃ q : QuaternionCentralProductData (Source.UH Z V₃),
      (center (Source.UH Z V₃)).map (Source.UH Z V₃).subtype = V₁
    rw [hspan]
    exact normal_quaternion_with_center d hA312 hH hU hn
  obtain ⟨q,hq⟩ := hq
  have h72 : Nat.card (Source.Hstar Z) ∣ 72 := by
    have hw : Nat.card BinaryFourPlus.Wreath = 72 :=
      (Nat.card_congr BinaryFourPlus.isometryEquivWreath.toEquiv).symm.trans
        BinaryFourPlus.card_isometrySubgroup
    rw [←hw]
    exact card_dvd_of_injective (hz.closureStarEmbedding q hq)
      (hz.closureStarEmbedding_injective q hq)
  have hcZ : Nat.card (pCore 2 Z) = 32 := by
    rw [←card_map_of_injective (K := pCore 2 Z) Z.subtype_injective]
    change Nat.card (Z.pCoreIn 2) = 32
    rw [normal_point_core_eq_closure d hA312 hH hU hn,←hspan]
    exact q.card
  have hZ : Nat.card Z ∣ 2304 := by
    have hh := (pCore 2 Z).card_mul_index
    rw [hcZ,index_eq_card] at hh
    rw [←hh]
    exact Nat.mul_dvd_mul_left 32 h72
  have hcH : Nat.card (pCore 2 H) = 32 := by
    rw [←card_map_of_injective (K := pCore 2 H) H.subtype_injective]
    change Nat.card (Source.QH H) = 32
    rw [normal_core_eq_closure d hA312 hH hU hn,←hspan]
    exact q.card
  have hHcard : 576 ∣ Nat.card H := by
    have hh := (pCore 2 H).card_mul_index
    rw [hcH,index_eq_card] at hh
    rw [←hh]
    exact Nat.mul_dvd_mul_left 32 (normal_star_card_multiple_eighteen d hA312 hH hU hn)
  let B := H.subgroupOf Z
  have hBcard : Nat.card B = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hH.2.1).toEquiv
  have hm : Nat.card H * B.index = Nat.card Z := by
    simpa only [hBcard] using B.card_mul_index
  have hi : B.index ∣ 4 := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 576)
    exact (Nat.mul_dvd_mul_right hHcard B.index).trans (hm ▸ hZ)
  let S : Sylow 2 Z := T.subtype hz.T_le_H
  have hSB : (S : Subgroup Z) ≤ B := by
    intro x hx
    have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
    exact hTH hx
  have hodd : ¬ 2 ∣ B.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hSB))
  have hcop : Nat.Coprime 4 B.index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left 2
  have he : B = ⊤ := index_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hi dvd_rfl)
  apply le_antisymm hH.2.1
  intro x hx
  have hb : (⟨x,hx⟩ : Z) ∈ B := by rw [he]; trivial
  exact hb

/-- The original quotient has precisely one of the two source orders. -/
theorem normal_star_card_cases :
    Nat.card (Source.Hstar H) = 18 ∨ Nat.card (Source.Hstar H) = 36 := by
  have hd := (normal_star_embedding d hA312 hH hU hn).2
  obtain ⟨k,hk⟩ := normal_star_card_multiple_eighteen d hA312 hH hU hn
  have hki : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 18)
    (show 18*k ∣ 18*2 from hk ▸ hd)
  rcases (Nat.dvd_prime Nat.prime_two).mp hki with he | he
  · left; simpa only [he,mul_one] using hk
  · right; simpa only [he] using hk

/-- The source local product L₁T has prime index three in H. -/
theorem normal_local_join_index :
    (residualCentralizer L V₁ ⊔ (T : Subgroup G)).relIndex H = 3 := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have h : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  let K := D.L₁ ⊔ (T : Subgroup G)
  let π := QuotientGroup.mk' (pCore 2 H)
  let A := Source.starImage H D.L₁
  let S := T.subtype h.T_le_H
  let R : Sylow 2 (Source.Hstar H) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  let : (D.L₁.subgroupOf H).Normal := hn
  let : A.Normal := Normal.map hn π (QuotientGroup.mk'_surjective _)
  have hA : Nat.card A = 3 := by
    change Nat.card (Source.starImage H (residualCentralizer L V₁)) = 3
    rw [Nat.card_congr (normal_residual_star_cubic d hA312 hH hU hn).toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
  have hstar : Nat.card (Source.Hstar H) = 9 * Nat.card R := by
    rw [R.card_eq_multiplicity]
    rcases normal_star_card_cases d hA312 hH hU hn with hc | hc <;>
      rw [hc] <;> decide +kernel
  have hdis : Disjoint A (R : Subgroup (Source.Hstar H)) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) _ _
      (IsPGroup.of_card (n := 1) (by simpa using hA)) R.isPGroup'
  have hcard : Nat.card (A ⊔ (R : Subgroup (Source.Hstar H)) : Subgroup (Source.Hstar H)) =
      3 * Nat.card R := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A R
      (by rw [A.normalizer_eq_top]; exact le_top) hdis,hA]
  have hindex : (A ⊔ (R : Subgroup (Source.Hstar H))).index = 3 := by
    have hm := (A ⊔ (R : Subgroup (Source.Hstar H))).card_mul_index
    rw [hcard,hstar] at hm
    have hp := Nat.card_pos (α := R)
    nlinarith
  have hk : π.ker ≤ K.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact mem_sup_right (h.QH_le_T (mem_map_of_mem H.subtype hx))
  have him : (K.subgroupOf H).map π = A ⊔ (R : Subgroup (Source.Hstar H)) := by
    rw [show K = D.L₁ ⊔ (T : Subgroup G) from rfl,
      subgroupOf_sup (le_sup_left.trans h.local_le) h.T_le_H,Subgroup.map_sup]
    rfl
  change (K.subgroupOf H).index = 3
  rw [←(K.subgroupOf H).index_map_eq (QuotientGroup.mk'_surjective _) hk,him]
  exact hindex

/-- All of original 13.5.15(6), with the original H_z and point centralizer. -/
theorem normal_source13_5_15_six :
    H = centralizer (V₁ : Set G) ∧
      Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
        (centralizer (V₁ : Set G)) (normalizer (L : Set G)) =
        {centralizer (V₁ : Set G)} := by
  have he := normal_eq_point_centralizer d hA312 hH hU hn
  refine ⟨he,Set.Subset.antisymm ?_ ?_⟩
  · intro J hJ
    have hKJ : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ J := hJ.1.2
    have hJH : J ≤ H := hJ.2.1.trans he.ge
    have hKH : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ H := hH.1.2
    have hKM : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
      sup_le (((map_subtype_le _).trans inf_le_left).trans L.le_normalizer) d.normalizes_L
    have hmax : IsCoatom ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf H) :=
      isCoatom_of_index_three _ (normal_local_join_index d hA312 hH hU hn)
    rcases hmax.le_iff.mp (subgroupOf_mono H hKJ) with ht | hh
    · have hh := congrArg (fun S : Subgroup H => S.map H.subtype) ht
      rw [map_subgroupOf_eq_of_le hJH,←MonoidHom.range_eq_map,H.range_subtype] at hh
      exact Set.mem_singleton_iff.mpr (hh.trans he)
    · have hh := congrArg (fun S : Subgroup H => S.map H.subtype) hh
      rw [map_subgroupOf_eq_of_le hJH,map_subgroupOf_eq_of_le hKH] at hh
      exact (hJ.2.2 (hh.le.trans hKM)).elim
  · rintro J (rfl : J = centralizer (V₁ : Set G))
    exact point_mem_family d hH

/-- The literal normalizer and involution-centralizer clauses used when
applying F.4.31 in 13.5.17, with both local cores already identified. -/
theorem normal_source13_5_17_local_groups :
    ∃ z : G, z ∈ V₁ ∧ orderOf z = 2 ∧ centralizer ({z} : Set G) = H ∧
      normalizer (V : Set G) = L ⊔ (T : Subgroup G) ∧
      H.pCoreIn 2 = Source.UH H V₃ ∧ (L ⊔ (T : Subgroup G)).pCoreIn 2 = V := by
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hh := d.flag.one_card
    rw [he,card_bot] at hh
    contradiction
  obtain ⟨⟨z,hz⟩,hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1 : z ≠ 1 := fun he => hz1 (Subtype.ext he)
  have ho : orderOf z = 2 := by
    have hd := V₁.orderOf_dvd_natCard hz
    rw [d.flag.one_card] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact (hz1 (orderOf_eq_one_iff.mp he)).elim
    · exact he
  have hline : V₁ = zpowers z := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_).symm
    rw [d.flag.one_card,Nat.card_zpowers,ho]
  refine ⟨z,hz,ho,?_,normal_module_normalizer_eq_local d hA312 hH hU hn,
    normal_core_eq_closure d hA312 hH hU hn,
    normal_local_core_eq_module d hA312 hH hU hn⟩
  rw [normal_eq_point_centralizer d hA312 hH hU hn,hline,
    zpowers_eq_closure,centralizer_closure]

end CFSG.Quasithin.Chapter13.Section05.A5Source
