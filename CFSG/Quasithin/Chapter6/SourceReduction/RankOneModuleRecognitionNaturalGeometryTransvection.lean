module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryInvolution
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The nontrivial transvection action in the odd critical geometry

At parameter two, put Q_z = <Z_S^{C_G(z)}> and W = U intersect Q_z.
The common-involution geometry makes W invariant under I. The moving
natural layer E meets W in the four-element endpoint line Z', so its
commutators on W lie in Z'. The kernel on W/<z> preserves Z' and therefore
normalizes O₂(C_G(Z')). Its intersection with that core lies in O₂(I).
Since E escapes O₂(H), this proves that E acts nontrivially on W/<z>.

The literal quotient action has an elementary actor image of order two
or four. Its displacement subgroup is exactly Z'/<z>, of order two, and
its second displacement is trivial. The kernel centralizes the I-closure
of E modulo that closure's two-core, supplying the next source input.

Initial naturalness, the later component and amalgam analysis proving
odd-branch nonabelianness, and the unconditional source 6.1.27 assembly
remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterE
variable {G : Type*} [Group G] [Finite G]

private theorem four_layer_intersection
    {E V U Z : Subgroup G} [IsElementaryAbelian 2 E]
    (hV : IsPGroup 2 V) (hVU : V ≤ U)
    (hab : U ≤ centralizer (U : Set G))
    (hZ : Z ≤ E ⊓ U) (hZcard : Nat.card Z = 4)
    (hEcard : Nat.card E = 16) (hsE : globalS E = 2)
    (hnon : ¬ V ≤ centralizer (E : Set G)) : E ⊓ U = Z := by
  apply (eq_of_le_of_card_ge hZ ?_).symm
  by_contra hc
  have hlarge : 4 < Nat.card (E ⊓ U : Subgroup G) := by omega
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup G) (E ⊓ U) E bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hEcard] at hprod
  have hi : (E ⊓ U).relIndex E < 4 := by nlinarith
  have hr : subgroupCorank E (E ⊓ U) < 2 :=
    (Nat.log_lt_iff_lt_pow (by decide) ((E ⊓ U).subgroupOf E).index_ne_zero_of_finite).mpr hi
  have he := centralizer_inf_eq_of_corank_lt_globalS
    (show E ⊓ U ≤ E from inf_le_left)
    (show (subgroupCorank E (E ⊓ U) : ℕ∞) < globalS E from by rw [hsE]; exact_mod_cast hr) hV
  apply hnon
  have hh : V ≤ V ⊓ centralizer (E : Set G) := by
    rw [←he]
    exact le_inf le_rfl (hVU.trans (hab.trans (centralizer_le inf_le_right)))
  exact hh.trans inf_le_right

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (f : G ≃* G) :
    (centralizer (A : Set G)).map f.toMonoidHom =
      centralizer (A.map f.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine mem_map.mpr ⟨f.symm x, ?_, f.apply_symm_apply x⟩
  apply mem_centralizer_iff.mpr
  intro a ha
  apply f.injective
  simpa using mem_centralizer_iff.mp hx (f a) (mem_map.mpr ⟨a,ha,rfl⟩)


omit [Finite G] in
private theorem closure_kernel_commutator
    {I E K : Subgroup G} (hEI : E ≤ I) (hKI : K ≤ I)
    (hIK : I ≤ Subgroup.normalizer (K : Set G))
    (hEK : ⁅E,K⁆ ≤ I.pCoreIn 2) :
    ⁅conjugateSpanBy E I,K⁆ ≤ (conjugateSpanBy E I).pCoreIn 2 := by
  let P := conjugateSpanBy E I
  have hPI : P ≤ I := conjugateSpanBy_le_self hEI
  have hIN : I ≤ Subgroup.normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPc : P ≤ commutatorPreimage I K (I.pCoreIn 2) :=
    conjugateSpanBy_le (le_commutatorPreimage hEI hEK)
      (commutatorPreimage_normalized I K (I.pCoreIn 2) I hIN I.le_normalizer hIK hIN)
  have hc : ⁅P,K⁆ ≤ I.pCoreIn 2 := (commutator_mono hPc le_rfl).trans
    (commutator_commutatorPreimage_le I K (I.pCoreIn 2) hIN)
  have hp : ⁅P,K⁆ ≤ P := le_normalizer_iff_commutator_le_left.mp
    (hKI.trans (le_normalizer_conjugateSpanBy E I))
  exact (le_inf hp hc).trans (inf_pCoreIn_le_of_le 2 hPI)

variable {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)

/-- The actual invariant intersection, moving natural layer and kernel
control under the contrary abelian-closure assumption of 6.1.19. -/
theorem exists_involution_transvection_geometry
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let U := Escape.U (T : Subgroup G) L R
      let Q := conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G))
      let W := U ⊓ Q
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let Z' := (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom
      let K := commutatorPreimage I W (zpowers z)
      E ≤ I ∧ z ∈ Z' ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      I ≤ Subgroup.normalizer (W : Set G) ∧
      ⁅E,W⁆ ≤ Z' ∧ ¬ ⁅E,W⁆ ≤ zpowers z ∧
      I ≤ Subgroup.normalizer (K : Set G) ∧
      ⁅E,K⁆ ≤ I.pCoreIn 2 := by
  obtain ⟨hn,hi⟩ := d.parameter_and_intersection h hnat hE hs hNS
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp
    ((one_lt_card_iff_ne_bot _).mp (hi ▸ (by decide : 1 < 2)))
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  let := h.ZS_elementary
  let := h.layer_elementary
  have ho : orderOf (z : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property.1) hz1
  obtain ⟨a,k,hplace,hVA,hout,hYi,hFi,hEY,hVF,hYF⟩ :=
    d.intersecting_hyperplanes h hnat hE hs hNS
  let I := Escape.I (T : Subgroup G) L R
  let U := Escape.U (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
  let C := centralizer ({(z : G)} : Set G)
  let Q := conjugateSpanBy Z C
  let W := U ⊓ Q
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let V := (layer L R).map (MulAut.conj (k : G)).toMonoidHom
  let Y := V ⊓ Subgroup.normalizer (E : Set G)
  let K := commutatorPreimage I W (zpowers (z : G))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hEI : E ≤ I := hplace.trans ((d.crossed_centralization h hnat hs).1.trans inf_le_right)
  have hVU : V ≤ U := hVA.trans d.closure_le
  have hZE : Z' ≤ E := hEY.symm.le.trans
    (le_normalizer_iff_commutator_le_left.mp (show Y ≤ Subgroup.normalizer (E : Set G) from inf_le_right))
  have hZU : Z' ≤ U := by
    apply hEY.symm.le.trans
    rw [commutator_comm]
    exact (commutator_mono (inf_le_left.trans hVU) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hEI.trans (NaturalEscape.I_normalizes_U _ _ _)))
  have hZcard : Nat.card Z' = 4 := by
    rw [card_map_of_injective (MulAut.conj d.representative).injective]
    have hh : Nat.card Z = 2 ^ n := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [hh,hn]
    norm_num
  have hEU : E ⊓ U = Z' := by
    apply four_layer_intersection (IsElementaryAbelian.isPGroup 2 V) hVU hab
      (le_inf hZE hZU) hZcard
    · rw [card_map_of_injective (MulAut.conj a).injective,hnat.card,hn]
      norm_num
    · rw [globalS_map_equiv (layer L R) (MulAut.conj a),hs,hn]
      norm_num
    · intro hc
      have hh := relIndex_eq_one.mpr (le_inf (le_refl E)
        ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)))
      rw [hFi] at hh
      norm_num at hh
  have hIC : I ≤ C := by
    intro i hi
    exact mem_centralizer_singleton_iff.mpr (hi (z : G) z.property.1).symm
  have hIZ : I ≤ Subgroup.normalizer (zpowers (z : G) : Set G) :=
    (show I ≤ centralizer (zpowers (z : G) : Set G) from
      centralizer_le (zpowers_le.mpr z.property.1)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c,hc,hline⟩ := natural_line_centralizer_transitive h hnat z.property.1 hz1 z.property.2
  have hZQ : Z' ≤ Q := by
    change Z.map (MulAut.conj d.representative).toMonoidHom ≤ conjugateSpanBy Z C
    change Z.map (MulAut.conj d.representative).toMonoidHom = Z.map (MulAut.conj c).toMonoidHom at hline
    rw [hline,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun t : C => Z.map (MulAut.conj (t : G)).toMonoidHom) ⟨c,hc⟩
  have hZW : Z' ≤ W := le_inf hZU hZQ
  have hEW : E ⊓ W = Z' := le_antisymm
    ((inf_le_inf_left E (show W ≤ U from inf_le_left)).trans hEU.le)
    (le_inf hZE hZW)
  have hIW : I ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf (NaturalEscape.I_normalizes_U _ _ _)
      (hIC.trans (le_normalizer_conjugateSpanBy Z C))).trans inf_normalizer_le_normalizer_inf
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) :=
    (natural_four_line_centralizer_closure h hnat hn z.property.1 hz1).1.trans
      ((natural_line_centralizer_core_geometry h hnat z.property.1 hz1).2 a (hZE z.property.2))
  have hcomm : ⁅E,W⁆ ≤ Z' := by
    rw [←hEW]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hQE))
      (le_normalizer_iff_commutator_le_right.mp (hEI.trans hIW))
  have hKI : K ≤ I := commutatorPreimage_le _ _ _
  have hIK : I ≤ Subgroup.normalizer (K : Set G) :=
    commutatorPreimage_normalized I W (zpowers (z : G)) I hIZ I.le_normalizer hIW hIZ
  have hKN : K ≤ Subgroup.normalizer (Z' : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk b hb
    have hh : ⁅k,b⁆ ∈ zpowers (z : G) :=
      commutator_commutatorPreimage_le I W (zpowers (z : G)) hIZ
        (commutator_mem_commutator hk (hZW hb))
    have he := Z'.mul_mem ((zpowers_le.mpr z.property.2) hh) hb
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using he
  let D := centralizer (Z' : Set G)
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := hKN.trans (normalizer_le_normalizer_centralizer Z')
  have hED : E ≤ D.pCoreIn 2 := by
    have hh := map_mono (f := (MulAut.conj d.representative).toMonoidHom)
      (d.closure_le.trans (natural_escape_core h hnat).1)
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj d.representative).injective] at hh
    change d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤
      ((centralizer (Z : Set G)).map (MulAut.conj d.representative).toMonoidHom).pCoreIn 2 at hh
    rw [centralizer_map_equiv Z (MulAut.conj d.representative)] at hh
    exact hplace.trans hh
  have hDK : D.pCoreIn 2 ⊓ K ≤ I.pCoreIn 2 := by
    have hh : D.pCoreIn 2 ⊓ K ≤ K.pCoreIn 2 := le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 D).to_le inf_le_left) inf_le_right
      ((le_inf (hKD.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
        K.le_normalizer).trans inf_normalizer_le_normalizer_inf)
    exact hh.trans (pCoreIn_mono_of_normalizes hKI hIK)
  have hEK : ⁅E,K⁆ ≤ I.pCoreIn 2 := by
    apply (le_inf ?_ ?_).trans hDK
    · exact (commutator_mono hED le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hKD.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))))
    · exact le_normalizer_iff_commutator_le_right.mp (hEI.trans hIK)
  have hnon : ¬ ⁅E,W⁆ ≤ zpowers (z : G) := by
    intro hh
    have hEK' : E ≤ K := le_commutatorPreimage hEI hh
    have hEQ : E ≤ I.pCoreIn 2 := (le_inf hED hEK').trans hDK
    apply hout
    have hTI : (T : Subgroup G) ≤ Subgroup.normalizer (I : Set G) :=
      h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z)
    obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T I hTI
    have hQT : I.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow I S
      rw [hS,subgroupOf_map_subtype] at hh
      exact hh.trans inf_le_left
    exact hEQ.trans (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
      (hQT.trans d.hstar.1.1.2)
      (d.overgroup.trans ((sup_le I.le_normalizer hTI).trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))))
  exact ⟨hn,z,a,z.property.1,ho,hEI,z.property.2,hZW,hEW,hIW,hcomm,hnon,hIK,hEK⟩

/-- The literal involution quotient carries a nontrivial elementary
transvection group of order at most four, with its exact common center.
The kernel is retained as an ambient commutator preimage for the ensuing
normal-closure and component arguments. -/
theorem exists_involution_transvection_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let Z' := (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom
      E ≤ I ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : ((zpowers z).subgroupOf W).Normal),
      letI := hN
      ∃ ρ : I →* MulAut (W ⧸ (zpowers z).subgroupOf W),
        (∀ i : I, ∀ w : W,
          ρ i (QuotientGroup.mk' ((zpowers z).subgroupOf W) w) =
            QuotientGroup.mk' ((zpowers z).subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
        IsElementaryAbelian 2 (W ⧸ (zpowers z).subgroupOf W) ∧
        IsElementaryAbelian 2 ((E.subgroupOf I).map ρ) ∧
        1 < Nat.card ((E.subgroupOf I).map ρ) ∧
        Nat.card ((E.subgroupOf I).map ρ) ≤ 4 ∧
        commutatorAction ((E.subgroupOf I).map ρ) (W ⧸ (zpowers z).subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' ((zpowers z).subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' ((zpowers z).subgroupOf W))) = 2 ∧
        commutatorAction₂ ((E.subgroupOf I).map ρ) (W ⧸ (zpowers z).subgroupOf W) = ⊥ ∧
        ρ.ker = (commutatorPreimage I W (zpowers z)).subgroupOf I ∧
        ⁅E,ρ.ker.map I.subtype⁆ ≤ I.pCoreIn 2 ∧
        ⁅conjugateSpanBy E I,ρ.ker.map I.subtype⁆ ≤ (conjugateSpanBy E I).pCoreIn 2 := by
  obtain ⟨hn,z,a,hz,ho,hEI,hz',hZW,hEW,hIW,hcomm,hnon,hIK,hEK⟩ :=
    d.exists_involution_transvection_geometry h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let U := Escape.U (T : Subgroup G) L R
  let W := U ⊓ conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let Z' := (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom
  let Z := zpowers z
  let K := commutatorPreimage I W Z
  have hZE : Z' ≤ E := hEW.ge.trans inf_le_left
  have hZc : Z ≤ Z' := zpowers_le.mpr hz'
  have hZW' : Z ≤ W := hZc.trans hZW
  have hIZc : I ≤ centralizer (Z : Set G) := centralizer_le (zpowers_le.mpr hz)
  have hIZ : I ≤ Subgroup.normalizer (Z : Set G) :=
    hIZc.trans (Subgroup.centralizer_le_normalizer _)
  have hWI : W ≤ I := inf_le_left.trans (Escape.U_centralizes_ZS h.layer_centralizes_ZS)
  let hN : (Z.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer (hWI.trans hIZ)
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action I W Z hIW hIZ hN
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  let A := (E.subgroupOf I).map ρ
  have hker : ρ.ker = K.subgroupOf I := by
    ext i
    change ρ i = 1 ↔ (i : G) ∈ K
    rw [mem_commutatorPreimage_iff I W Z hIZ]
    constructor
    · intro hi
      refine ⟨i.property,fun w hw => ?_⟩
      have hh := congrArg (fun f : MulAut (W ⧸ Z.subgroupOf W) => f (q ⟨w,hw⟩)) hi
      rw [hρ] at hh
      have hz := QuotientGroup.eq_iff_div_mem.mp hh
      change (i : G) * w * (i : G)⁻¹ / w ∈ Z at hz
      simpa only [commutatorElement_def,div_eq_mul_inv] using hz
    · rintro ⟨_,hc⟩
      ext w
      obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) w
      rw [hρ]
      apply QuotientGroup.eq_iff_div_mem.mpr
      change (i : G) * (w : G) * (i : G)⁻¹ / (w : G) ∈ Z
      simpa only [commutatorElement_def,div_eq_mul_inv] using hc w w.property
  let := h.layer_elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (E.subgroupOf I) := IsElementaryAbelian.subgroupOf hEI
  have hAelem : IsElementaryAbelian 2 A := IsElementaryAbelian.map ρ
  have hUelem : IsElementaryAbelian 2 U := by
    have he : U = conjugateSpanBy (layer L R) I := by
      rw [conjugateSpanBy_eq_iSup_conj]; rfl
    let : IsMulCommutative (conjugateSpanBy (layer L R) I) :=
      he ▸ le_centralizer_iff_isMulCommutative.mp hab
    rw [he]
    exact conjugateSpanBy_elementary_of_commutative _ _
  let := hUelem
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ U from inf_le_left)
  have hquot : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) :=
    IsElementaryAbelian.of_surjective q (QuotientGroup.mk'_surjective _)
  have hAcard : Nat.card A = K.relIndex E := by
    rw [←relIndex_ker,hker,relIndex_subgroupOf hEI]
  have hApos : 1 < Nat.card A := by
    rw [hAcard]
    have hne : K.relIndex E ≠ 1 := by
      intro he
      exact hnon ((commutator_mono (relIndex_eq_one.mp he) le_rfl).trans
        (commutator_commutatorPreimage_le I W Z hIZ))
    have hp : K.relIndex E ≠ 0 := (K.subgroupOf E).index_ne_zero_of_finite
    change 1 < K.relIndex E
    omega
  have hZcard : Nat.card Z' = 4 := by
    rw [card_map_of_injective (MulAut.conj d.representative).injective]
    have hh : Nat.card (ZS (T : Subgroup G) L R) = 2 ^ n :=
      (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [hh,hn]
    norm_num
  have hEcard : Nat.card E = 16 := by
    rw [card_map_of_injective (MulAut.conj a).injective,hnat.card,hn]
    norm_num
  have hZidx : Z'.relIndex E = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Z' E bot_le hZE
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,hEcard] at hh
    omega
  have hZK : Z' ≤ K := le_commutatorPreimage (hZE.trans hEI) (by
    have hh : ⁅Z',W⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      ((hZW.trans inf_le_left).trans (hab.trans (centralizer_le inf_le_left)))
    rw [hh]; exact bot_le)
  have hAupper : Nat.card A ≤ 4 := by
    rw [hAcard,←hZidx]
    exact relIndex_le_of_le_left hZK (Z'.subgroupOf E).index_ne_zero_of_finite
  have hlinecard : Nat.card ((Z'.subgroupOf W).map q) = 2 := by
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hZW]
    change Z.relIndex Z' = 2
    have hzcard : Nat.card Z = 2 := by rw [Nat.card_zpowers,ho]
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Z Z' bot_le hZc
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,hzcard] at hh
    omega
  have hdisp := quotient_conjugation_commutatorAction_eq_image I W Z E hIW hEI hN ρ hρ
  have hdisple : commutatorAction A (W ⧸ Z.subgroupOf W) ≤ (Z'.subgroupOf W).map q := by
    rw [hdisp]
    exact map_mono (subgroupOf_mono W (by rwa [commutator_comm] : ⁅W,E⁆ ≤ Z'))
  have hdispCard := quotient_conjugation_commutatorAction_card I W Z E hIW hEI hN ρ hρ
  have hdispPos : 1 < Nat.card (commutatorAction A (W ⧸ Z.subgroupOf W)) := by
    rw [hdispCard]
    have hne : Z.relIndex ⁅W,E⁆ ≠ 1 := by
      intro he
      have hh : ⁅W,E⁆ ≤ Z := relIndex_eq_one.mp he
      rw [commutator_comm W E] at hh
      exact hnon hh
    have hp : Z.relIndex ⁅W,E⁆ ≠ 0 := (Z.subgroupOf ⁅W,E⁆).index_ne_zero_of_finite
    change 1 < Z.relIndex ⁅W,E⁆
    omega
  have hdispEq : commutatorAction A (W ⧸ Z.subgroupOf W) = (Z'.subgroupOf W).map q :=
    eq_of_le_of_card_ge hdisple (by rw [hlinecard]; omega)
  have hdouble : ⁅⁅W,E⁆,E⁆ ≤ Z := by
    have hh : ⁅Z',E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hZE.trans (le_centralizer E))
    have hh' := commutator_mono (by rwa [commutator_comm] : ⁅W,E⁆ ≤ Z') (le_refl E)
    exact hh'.trans (hh ▸ bot_le)
  have hquadratic := quotient_conjugation_quadratic_of_double_commutator_le I W Z E
    hIW hEI hN hdouble ρ hρ
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hEW,hIW,hN,ρ,hρ,hquot,hAelem,hApos,hAupper,
    hdispEq,hlinecard,hquadratic,hker,?_,?_⟩
  · rw [hker,map_subgroupOf_eq_of_le (commutatorPreimage_le I W Z)]
    exact hEK
  · rw [hker,map_subgroupOf_eq_of_le (commutatorPreimage_le I W Z)]
    exact closure_kernel_commutator hEI (commutatorPreimage_le I W Z) hIK hEK

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
