module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelSpan
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# An elementary characteristic envelope for the original fixed subgroup

Every involution of the kernel core has action image either one or the
unique center-fixing involution t of the original Sylow image. It therefore
centralizes E=Fix(t). Thus J(Q) centralizes E, and maximum elementary
saturation puts E inside A=Ω₁Z(J(Q)). This characteristic envelope is
normalized by Mc, so it contains the full C_G(U)-span F of E. In particular
F is elementary even when V is not contained in Q.
No containment of V in the envelope and no equality F=E is asserted.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Section02.ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

private theorem center_fixing_involution_eq
    (P : Subgroup G) [P.Normal] [IsExtraspecial 3 P] (hP : Nat.card P = 27)
    (hC : centralizer (P : Set G) ≤ P) (S : Sylow 2 G)
    (a t : G) (haS : a ∈ (S : Subgroup G)) (htS : t ∈ (S : Subgroup G))
    (ha : orderOf a = 2) (ht : orderOf t = 2)
    (haC : a ∈ centralizer ((center P).map P.subtype : Set G))
    (htC : t ∈ centralizer ((center P).map P.subtype : Set G)) : a = t := by
  have hfix (s : G) (hs : s ∈ centralizer ((center P).map P.subtype : Set G)) :
      ∀ z ∈ center P, (MulAut.conjNormal s : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    change s * (z : G) * s⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (hs z (mem_map_of_mem P.subtype hz)).symm
  have hprod : a*t ∈ P := IsExtraspecial.involution_mul_mem_of_card27 P hP hC a t
    ⟨by intro he; simp [he] at ha,by simpa only [ha] using pow_orderOf_eq_one a⟩
    ⟨by intro he; simp [he] at ht,by simpa only [ht] using pow_orderOf_eq_one t⟩
    (hfix a haC) (hfix t htC)
  have hdis : Disjoint P (S : Subgroup G) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    rw [hP,hn]
    exact (by decide : Nat.Coprime 27 2).pow_right n
  have he : a*t=1 := mem_bot.mp (hdis.eq_bot ▸
    (show a*t ∈ P ⊓ (S : Subgroup G) from ⟨hprod,(S : Subgroup G).mul_mem haS htS⟩))
  have ht2 : t*t=1 := by simpa only [pow_two,ht] using pow_orderOf_eq_one t
  exact (eq_inv_of_mul_eq_one_left he).trans (inv_eq_of_mul_eq_one_right ht2)

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_maxJ_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let Q := (centralizer (U : Set G)).pCoreIn 2
    let f := (actionHom M V h.normalized).rangeRestrict
    ((elementaryAbelianMaxJ Q).subgroupOf M).map f ≤
      ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Q := (centralizer (U : Set G)).pCoreIn 2
  let E := thompsonFixed T V
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V h.normalized).rangeRestrict_surjective
  let B := (Q.subgroupOf M).map f
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  let S : Sylow 2 D := (T.subtype hM.1.2).mapSurjective hf
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQT : Q ≤ (T : Subgroup G) := hcore.2.1
  have hQM := hQT.trans hM.1.2
  have hBS : B≤(S : Subgroup D) := map_mono (subgroupOf_mono M hQT)
  have hQnorm : Mc ≤ normalizer (Q : Set G) := by
    change Mc ≤ normalizer ((centralizer (U : Set G)).pCoreIn 2 : Set G)
    rw [hcore.1]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  obtain ⟨t,ht,htR,hr⟩ := h.extraspecial_small_thompson_image
    hG T hempty hM hmany hJ hfull hex
  change zpowers t=R at htR
  change fixedCodim ρ R=2 at hr
  have htS : t∈(S : Subgroup D) :=
    (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))) (htR ▸ mem_zpowers t)
  have hDcore : pCore 2 D=⊥ := by
    subst V
    exact source_localAction_twoCore hG T hM
  obtain ⟨_,_,_,hP,hPc,_,h6,_⟩ := hex
  let : IsExtraspecial 3 P := hP
  have hZc : Nat.card ZP=3 := by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have htZ : t∈centralizer (ZP : Set D) :=
    ExtraspecialBinarySix.small_involution_centralizes_center ρ
      (imageRepresentation_injective M V h.normalized) P hPc h6 t
      (by simpa only [ht] using pow_orderOf_eq_one t) (by rw [htR]; exact hr.le)
  have hZR : ZP≤normalizer (R : Set D) := by
    rw [←htR]
    exact (le_centralizer_iff.mp (zpowers_le.mpr htZ)).trans
      (Subgroup.centralizer_le_normalizer _)
  let WU := subspaceCommutator ρ ⊤ R
  have hZstable : ZP≤subspaceStabilizer ρ WU :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hZR
  have hUambient := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2)
  change ambientSpace V WU=U at hUambient
  have hZpre : (ZP.comap f).map M.subtype≤Mc := by
    rw [hmod.2]
    change (ZP.comap f).map M.subtype≤normalizer (U : Set G)
    rw [←hUambient]
    apply le_normalizer_iff.mpr
    rintro _ ⟨m,hm,rfl⟩ _ ⟨v,hv,rfl⟩
    exact ⟨(ρ (f m) (Additive.ofMul v)).toMul,
      (hZstable hm (Additive.ofMul v)).2 hv,rfl⟩
  have hZB : ZP≤normalizer (B : Set D) := by
    intro z hz
    obtain ⟨m,hm⟩ := hf z
    have hmMc : (m : G)∈Mc := hZpre ⟨m,show f m∈ZP from hm.symm ▸ hz,rfl⟩
    have hmQ : m∈normalizer (Q.subgroupOf M : Set M) := by
      rw [←subgroupOf_normalizer_eq hQM]
      exact hQnorm hmMc
    exact hm ▸ (Q.subgroupOf M).le_normalizer_map f (mem_map_of_mem f hmQ)
  have hB2 : IsPGroup 2 B := (isPGroup_pCoreIn 2 _).comap_subtype.map f
  have hZ3 : IsPGroup 3 ZP := IsPGroup.of_card (n := 1) hZc
  have hBC : B≤centralizer (ZP : Set D) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hZB)
      (le_normalizer_iff_commutator_le_right.mp (show B≤normalizer (ZP : Set D) from
        le_normalizer_of_normal))).trans
      (hB2.disjoint_of_coprime hZ3 (by decide)).le_bot
  have hJpull : elementaryAbelianMaxJ Q≤(R.comap f).map M.subtype := by
    apply sSup_le
    intro A hA
    let : IsElementaryAbelian 2 A := hA.2.1
    intro a ha
    have haQ : a∈Q := hA.1 ha
    let am : M := ⟨a,hQM haQ⟩
    have haB : f am∈B := mem_map_of_mem f haQ
    have ha2 : (f am)^2=1 := by
      rw [←map_pow]
      have he : am^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
      rw [he,map_one]
    have haR : f am∈R := by
      by_cases ha1 : f am=1
      · exact ha1 ▸ one_mem _
      · have he := center_fixing_involution_eq P hPc
          (centralizer_pResidual_le_of_pCore_eq_bot hDcore) S (f am) t
          (hBS haB) htS (orderOf_eq_prime ha2 ha1) ht (hBC haB) htZ
        rw [he,←htR]
        exact mem_zpowers t
    exact ⟨am,haR,rfl⟩
  change ((elementaryAbelianMaxJ Q).subgroupOf M).map f≤R
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨b,hb,he⟩ := hJpull ha
  have hba : b=a := Subtype.ext he
  exact hba ▸ hb

omit [Finite G] in
private theorem kernel_envelope_normalizer (Q : Subgroup G) :
    normalizer (Q : Set G) ≤
      normalizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hQg : Q.map (MulAut.conj g).toMonoidHom=Q :=
    mem_normalizer_iff_map_conj_eq.mp hg
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ Q)).map
    (MulAut.conj g).toMonoidHom=omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    ←elementaryAbelianMaxJ_map_equiv,hQg]

/-- The original fixed subgroup and all its kernel conjugates lie in a
characteristic elementary envelope of Q, normalized by the actual partner. -/
theorem PreparedChosenModule.extraspecial_kernel_fixed_envelope
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let E := thompsonFixed T V
    let C := centralizer (U : Set G)
    let Q := C.pCoreIn 2
    let F := conjugateSpanBy E C
    let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
    elementaryAbelianMaxJ Q≤centralizer (E : Set G) ∧ E≤A ∧ F≤A ∧
      IsElementaryAbelian 2 F ∧ Mc≤normalizer (A : Set G) := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let E := thompsonFixed T V
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy E C
  let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQM : Q≤M := hcore.2.1.trans hM.1.2
  let f := (actionHom M V h.normalized).rangeRestrict
  let ρ := imageRepresentation M V h.normalized
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  have hJR : ((elementaryAbelianMaxJ Q).subgroupOf M).map f≤R :=
    kernel_maxJ_image hG T hempty hM hmany hJ hu h hfull hex
  have hJQ : elementaryAbelianMaxJ Q≤Q := sSup_le fun _ hA => hA.1
  have hJM := (ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2
  have hEambient := ambientSpace_fixed h.normalized hJM
  change ambientSpace V (fixedSpace ρ R)=E at hEambient
  have hJE : elementaryAbelianMaxJ Q≤centralizer (E : Set G) := by
    intro a ha e he
    let am : M := ⟨a,hQM (hJQ ha)⟩
    have haR : f am∈R := hJR (mem_map_of_mem f ha)
    let ev : V := ⟨e,he.1⟩
    have hv : Additive.ofMul ev∈fixedSpace ρ R :=
      (mem_ambientSpace (fixedSpace ρ R) ev).mp (hEambient.symm ▸ he)
    have heq := congrArg (fun w : Additive V => (w.toMul : G)) (hv ⟨f am,haR⟩)
    change a*e*a⁻¹=e at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E≤V from inf_le_left)
  have hEQ : E≤Q := h.extraspecial_moved_fixed_le_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hEA : E≤A := elementary_centralizer_maxJ_le_omegaCenter Q E hEQ
    (le_centralizer_iff.mp hJE)
  have hMcQ : Mc≤normalizer (Q : Set G) := by
    change Mc≤normalizer (C.pCoreIn 2 : Set G)
    rw [hcore.1]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hMcA : Mc≤normalizer (A : Set G) := hMcQ.trans (kernel_envelope_normalizer Q)
  have hCMc : C≤Mc := by
    rw [(h.extraspecial_partner_module_and_normalizer
      hG T hempty hM hmany hJ hu hfull hex).2]
    exact Subgroup.centralizer_le_normalizer _
  have hFA : F≤A := conjugateSpanBy_le hEA (hCMc.trans hMcA)
  let : IsElementaryAbelian 2 A := omegaOneCenterAmbient_elementaryAbelian _
  exact ⟨hJE,hEA,hFA,IsElementaryAbelian.of_le hFA,hMcA⟩

/-- The full module moves the original kernel span only inside U,
without either core-intersection row as an extra premise. -/
theorem PreparedChosenModule.extraspecial_kernel_span_full_displacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let F := conjugateSpanBy (thompsonFixed T V) (centralizer (U : Set G))
    ⁅V,F⁆≤U := by
  let := h.elementary
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy (thompsonFixed T V) C
  let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  let f := (actionHom M V h.normalized).rangeRestrict
  let ρ := imageRepresentation M V h.normalized
  let R := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  have hen := h.extraspecial_kernel_fixed_envelope hG T hempty hM hmany hJ hu hfull hex
  have hFA : F≤A := hen.2.2.1
  have hAJ : A≤elementaryAbelianMaxJ Q := by
    intro a ha
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp ha).1
  have hFJ := hFA.trans hAJ
  have hJQ : elementaryAbelianMaxJ Q≤Q := sSup_le fun _ hA => hA.1
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hFM : F≤M := hFJ.trans (hJQ.trans (hcore.2.1.trans hM.1.2))
  have hJR : ((elementaryAbelianMaxJ Q).subgroupOf M).map f≤R :=
    kernel_maxJ_image hG T hempty hM hmany hJ hu h hfull hex
  have hFR : (F.subgroupOf M).map f≤R :=
    (map_mono (subgroupOf_mono M hFJ)).trans hJR
  have hspaces : subspaceCommutator ρ ⊤ ((F.subgroupOf M).map f)≤subspaceCommutator ρ ⊤ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,hv,rfl⟩
    exact Submodule.subset_span ⟨b,hFR hb,v,hv,rfl⟩
  have hFambient := ambientSpace_moved h.normalized h.le_selected hFM
  have hUambient := ambientSpace_moved h.normalized h.le_selected
    ((ChapterB.thompsonJ_le (T : Subgroup G) 1).trans hM.1.2)
  change ambientSpace V (subspaceCommutator ρ ⊤ ((F.subgroupOf M).map f))=⁅V,F⁆ at hFambient
  change ambientSpace V (subspaceCommutator ρ ⊤ R)=U at hUambient
  change ⁅V,F⁆≤U
  rw [←hFambient,←hUambient]
  rintro _ ⟨v,hv,rfl⟩
  exact ⟨v,hspaces hv,rfl⟩

end CFSG.Quasithin.Chapter15.Section01
