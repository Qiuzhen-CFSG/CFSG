module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Span
public import CFSG.Quasithin.ChapterB.Section02.QuadraticSubactor
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.GeneratorEstimates
public import Theory.Representation.BinaryOffender.InternalGenerators
public import Theory.GroupTheory.MaxElementaryConjugateSpan
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The original ratio-two budget on the partner's full-module span

In the contained-core branch the actual span of V is elementary and normal
under Mc. Its conjugate generators retain the original quadratic-ratio bound
under any subgroup of O₂(Mc). Applying the generating filtration to a genuine
quadratic maximum actor bounds its action from inside the core by its image
outside the core. No quotient of the span by V or E is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

private theorem core_generator_sequence (M N V Q H : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 H]
    (hMV : M≤normalizer (V:Set G)) (hQM : Q≤M)
    (hNQ : N≤normalizer (Q:Set G))
    (hHN : H≤N) (hNH : N≤normalizer (H:Set G))
    (hspan : H=conjugateSpan N V) (B : Subgroup N)
    (hBQ : B.map N.subtype≤Q) :
    let U := H.subgroupOf N
    let : U.Normal := normal_subgroupOf_of_le_normalizer hNH
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hHN
    ∃ (n : ℕ) (W : ℕ→Subrepresentation ((normalRepresentation U).comp B.subtype)),
      generatingSpan _ W n=⊤ ∧ ∀ i<n,
        quadraticRatio (imageRepresentation M V hMV)≤
          quadraticRatio (Representation.BinaryOffender.imageRepresentation (W i).toRepresentation) := by
  let U := H.subgroupOf N
  let : U.Normal := normal_subgroupOf_of_le_normalizer hNH
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hHN
  let Wg (g:N) := V.map (MulAut.conj (g:G)).toMonoidHom
  let W (g:N) := (Wg g).subgroupOf N
  have hWH (g:N) : Wg g≤H := by
    rw [hspan]
    exact le_iSup (fun x:N=>V.map (MulAut.conj (x:G)).toMonoidHom) g
  have hWN (g:N) : Wg g≤N := (hWH g).trans hHN
  have hWU (g:N) : W g≤U := fun _ hx=>(hWH g) hx
  have hBW (g:N) : B≤normalizer (W g:Set N) := by
    have hn : Q≤normalizer (V:Set G) := hQM.trans hMV
    have he : Q.map (MulAut.conj (g:G)).toMonoidHom=Q :=
      mem_normalizer_iff_map_conj_eq.mp (hNQ g.property)
    have hn' : Q≤normalizer (Wg g:Set G) := by
      rw [←he]
      exact (map_mono hn).trans (le_normalizer_map _)
    apply le_trans _ (le_normalizer_comap N.subtype)
    intro b hb
    exact hn' (hBQ (mem_map_of_mem N.subtype hb))
  let J (g:N) := internalGenerator U B (W g) (hBW g)
  have hgen : (⨆ g:N,W g)=U := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_iSup,map_subgroupOf_eq_of_le hHN]
    simp_rw [W,map_subgroupOf_eq_of_le (hWN _)]
    exact hspan.symm
  have hr (g:N) : quadraticRatio (imageRepresentation M V hMV)≤
      quadraticRatio (Representation.BinaryOffender.imageRepresentation (J g).toRepresentation) := by
    let : IsElementaryAbelian 2 (Wg g) := IsElementaryAbelian.map _
    let : IsElementaryAbelian 2 (W g) := IsElementaryAbelian.subgroupOf (hWN g)
    let e := (subgroupOfEquivOfLe (hWN g)).trans
      ((MulAut.conj (g:G)).subgroupMap V).symm
    let E₀ : Additive (W g) ≃ₗ[ZMod 2] Additive V :=
      LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
    let E : (J g).toSubmodule ≃ₗ[ZMod 2] Additive V :=
      (internalGeneratorEquiv U B (W g) (hBW g) (hWU g)).symm.trans E₀
    let f₀ : B→*G := (MulAut.conj (g:G)⁻¹).toMonoidHom.comp (N.subtype.comp B.subtype)
    have hf₀ (b:B) : f₀ b∈M := hQM (le_normalizer_iff.mp hNQ
      (g:G)⁻¹ (N.inv_mem g.property) (b.val:G)
      (hBQ (mem_map_of_mem N.subtype b.property)))
    let f := (actionHom M V hMV).rangeRestrict.comp (f₀.codRestrict M hf₀)
    have hEval (v:(J g).toSubmodule) :
        ((E v).toMul:G)=(g:G)⁻¹*(v.val.toMul.val:G)*(g:G) := by
      obtain ⟨w,rfl⟩ := (internalGeneratorEquiv U B (W g) (hBW g) (hWU g)).surjective v
      change ((E₀ ((internalGeneratorEquiv U B (W g) (hBW g) (hWU g)).symm
        ((internalGeneratorEquiv U B (W g) (hBW g) (hWU g)) w))).toMul:G)=_
      rw [LinearEquiv.symm_apply_apply]
      rfl
    apply quadraticRatio_le_image_of_equivariant _ _ f
      (imageRepresentation_injective M V hMV) E
    intro b v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hEval]
    change (g:G)⁻¹*((b.val:G)*(v.val.toMul.val:G)*(b.val:G)⁻¹)*(g:G)=
      f₀ b*((E v).toMul:G)*(f₀ b)⁻¹
    rw [hEval]
    change (g:G)⁻¹*((b.val:G)*(v.val.toMul.val:G)*(b.val:G)⁻¹)*(g:G)=
      ((g:G)⁻¹*(b.val:G)*((g:G)⁻¹)⁻¹)*
        ((g:G)⁻¹*(v.val.toMul.val:G)*(g:G))*
          ((g:G)⁻¹*(b.val:G)*((g:G)⁻¹)⁻¹)⁻¹
    group
  have hg : (⨆ g:N,J g)=⊤ := iSup_internalGenerator_eq_top U B W hBW hWU hgen
  obtain ⟨n,a,ha⟩ := exists_generatingSequence _ J hg
  exact ⟨n,fun i=>J (a i),ha,fun i _=>hr (a i)⟩

private theorem action_rank_upper (U A Q : Subgroup G)
    [IsElementaryAbelian 2 A] :
    Nat.log 2 ((centralizer (U:Set G)).relIndex A) ≤
      Nat.log 2 (Q.relIndex A)+
        Nat.log 2 ((centralizer (U:Set G)).relIndex (A⊓Q)) := by
  let B := A⊓Q
  let C := A⊓centralizer (U:Set G)
  let D := B⊓centralizer (U:Set G)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (inf_le_left : B≤A)
  have ha := rank_sub_rank_eq_log_relIndex A C (inf_le_left : C≤A)
  have hb := rank_sub_rank_eq_log_relIndex B D (inf_le_left : D≤B)
  have hab := rank_sub_rank_eq_log_relIndex A B (inf_le_left : B≤A)
  have hDC : D≤C := inf_le_inf_right _ (inf_le_left : B≤A)
  have hr : (rank D:ℝ)≤rank C := by
    exact_mod_cast Nat.log_mono_right (Subgroup.card_le_of_le hDC)
  dsimp only [C] at ha
  dsimp only [D] at hb
  dsimp only [B] at hab
  rw [inf_relIndex_left] at ha hb hab
  have hh : (Nat.log 2 ((centralizer (U:Set G)).relIndex A):ℝ)≤
      (Nat.log 2 (Q.relIndex A):ℝ)+
        (Nat.log 2 ((centralizer (U:Set G)).relIndex B):ℝ) := by linarith
  exact_mod_cast hh

/-- The genuine maximum quadratic actor on the actual partner span obeys
the ratio-two bound on its core intersection and the independent outside-rank
budget. The centralizer kernel is retained literally throughout. -/
theorem PreparedChosenModule.partner_core_quadratic_actor_budget
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G))={Mc})
    (hne : M≠Mc) (h : PreparedChosenModule T M V) (hVQ : V≤Mc.pCoreIn 2) :
    let H := conjugateSpanBy V (centralizer (localModule T Mc:Set G))
    ∃ (hn : Mc≤normalizer (H:Set G)) (he : IsElementaryAbelian 2 H) (hle : H≤Mc),
      letI := he
      let U := H.subgroupOf Mc
      letI : U.Normal := normal_subgroupOf_of_le_normalizer hn
      letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hle
      ∃ A∈elementaryAbelianMaxSubgroups ((T:Subgroup G).subgroupOf Mc),
        ¬A≤pCore 2 Mc ∧ A.map Mc.subtype≤centralizer (V:Set G) ∧
        ¬A≤centralizer (U:Set Mc) ∧ IsQuadratic (normalRepresentation U) A ∧
        let B := A⊓pCore 2 Mc
        2*Nat.log 2 ((centralizer (U:Set Mc)).relIndex B)≤
          fixedCodim (normalRepresentation U) B ∧
        fixedCodim (normalRepresentation U) B≤fixedCodim (normalRepresentation U) A ∧
        fixedCodim (normalRepresentation U) A≤
          Nat.log 2 ((centralizer (U:Set Mc)).relIndex A) ∧
        Nat.log 2 ((centralizer (U:Set Mc)).relIndex B)≤
          Nat.log 2 ((pCore 2 Mc).relIndex A) := by
  let C := centralizer (localModule T Mc:Set G)
  let H := conjugateSpanBy V C
  let Q := Mc.pCoreIn 2
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz=>(centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hQT : Q≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] at hh
  have hMcQ : Mc≤normalizer (Q:Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  obtain ⟨hn,he,hVH,hHcore,hHV,hmove,hff⟩ :=
    h.partner_core_span_ff hG T hempty hM hJ hu hne hVQ
  let := he
  let := h.elementary
  have hHN : H≤Mc := (hHcore.trans inf_le_right).trans (pCoreIn_le 2 Mc)
  have hHT : H≤(T:Subgroup G) := (hHcore.trans inf_le_right).trans hQT
  have hCMc : C≤Mc := localModule_centralizer_le_partner T Mc hu
  have hspan : H=conjugateSpan Mc V := by
    rw [conjugateSpan_eq]
    exact le_antisymm (conjugateSpanBy_mono le_rfl hCMc)
      (conjugateSpanBy_le hVH.le hn)
  let U := H.subgroupOf Mc
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hHN
  let S := (T:Subgroup G).subgroupOf Mc
  have hUS : U≤S := fun _ hx=>hHT hx
  have hall : ∀ D∈elementaryAbelianMaxSubgroups (T:Subgroup G),
      D≤centralizer (V:Set G) :=
    fun D hD=>(le_sSup hD).trans (hJ.trans (centralizer_le h.le_local))
  have hinside : ∀ A∈elementaryAbelianMaxSubgroups S,
      A≤pCore 2 Mc → A≤centralizer (U:Set Mc) := by
    intro A hA hAQ
    have hAm : A.map Mc.subtype∈elementaryAbelianMaxSubgroups (T:Subgroup G) := by
      rw [←map_subgroupOf_eq_of_le hTMc]
      exact (maxFamily_map_injective_iff Mc.subtype Mc.subtype_injective S A).mpr hA
    have hc := maxElementary_inside_centralizes_conjugateSpan (T:Subgroup G) Q V C
      (A.map Mc.subtype) hQT (hCMc.trans hMcQ) hall hAm (map_mono hAQ)
    intro a ha u hu
    exact Subtype.ext (hc (mem_map_of_mem Mc.subtype ha) u hu)
  have hex : ∃ A∈elementaryAbelianMaxSubgroups S,
      ¬A≤centralizer (U:Set Mc) := by
    by_contra! hh
    have hj : elementaryAbelianMaxJ S≤centralizer (U:Set Mc) := sSup_le hh
    apply hmove
    have hm := map_mono (f:=Mc.subtype) hj
    rw [←elementaryAbelianMaxJ_map_injective Mc.subtype Mc.subtype_injective,
      map_subgroupOf_eq_of_le hTMc] at hm
    intro a ha u hu
    obtain ⟨am,ham,heq⟩ := hm ha
    have hc : am∈centralizer (U:Set Mc) := ham
    have hh := congrArg Mc.subtype (hc ⟨u,hHN hu⟩ hu)
    change u*(am:G)=(am:G)*u at hh
    change (am:G)=a at heq
    rw [heq] at hh
    exact hh
  obtain ⟨A₀,hA₀,hn₀⟩ := hex
  obtain ⟨A,hA,hnA,hquad,hsub⟩ :=
    ChapterB.maxElementary_exists_quadratic_subactor U S A₀ hUS hA₀ hn₀
  have hAQ : ¬A≤pCore 2 Mc := fun hh=>hnA (hinside A hA hh)
  have hAV : A.map Mc.subtype≤centralizer (V:Set G) := by
    apply hall
    rw [←map_subgroupOf_eq_of_le hTMc]
    exact (maxFamily_map_injective_iff Mc.subtype Mc.subtype_injective S A).mpr hA
  let B := A⊓pCore 2 Mc
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le (inf_le_left : B≤A)
  obtain ⟨n,W,hgen,hr⟩ := core_generator_sequence M Mc V Q H h.normalized
    (hQT.trans hM.1.2) hMcQ hHN hn hspan B
    (map_mono (inf_le_right : B≤pCore 2 Mc))
  have hratio : ∀ i<n, (2:ℝ≥0∞)≤quadraticRatio
      (Representation.BinaryOffender.imageRepresentation (W i).toRepresentation) := by
    intro i hi
    rw [←h.quadratic_ratio]
    exact hr i hi
  have hquadB : IsQuadratic (normalRepresentation U) B :=
    fun a ha b hb v=>hquad a ha.1 b hb.1 v
  have hlo := MultipleFactors.generator_rank_bound U B W 2 n (by norm_num) hgen hquadB hratio
  rw [qrcActionKernel_eq_centralizer,←index_eq_card] at hlo
  norm_num only [ENNReal.toReal_ofNat] at hlo
  have hl : 2*Nat.log 2 ((centralizer (U:Set Mc)).relIndex B)≤
      fixedCodim (normalRepresentation U) B := by exact_mod_cast hlo
  have hm : fixedCodim (normalRepresentation U) B≤fixedCodim (normalRepresentation U) A := by
    have hh : fixedSpace (normalRepresentation U) A≤fixedSpace (normalRepresentation U) B := by
      intro v hv b
      exact hv ⟨b,b.property.1⟩
    have hdim := Submodule.finrank_mono hh
    have ha := fixedCodim_add_finrank (normalRepresentation U) A
    have hb := fixedCodim_add_finrank (normalRepresentation U) B
    omega
  have ha := MultipleFactors.maxElementary_fixedCodim_le U S A hUS hA
  have hupper := action_rank_upper U A (pCore 2 Mc)
  have hbudget : Nat.log 2 ((centralizer (U:Set Mc)).relIndex B)≤
      Nat.log 2 ((pCore 2 Mc).relIndex A) := by
    change Nat.log 2 ((centralizer (U:Set Mc)).relIndex A)≤
      Nat.log 2 ((pCore 2 Mc).relIndex A)+
        Nat.log 2 ((centralizer (U:Set Mc)).relIndex B) at hupper
    omega
  exact ⟨hn,he,hHN,A,hA,hAQ,hAV,hnA,hquad,hl,hm,ha,hbudget⟩

end CFSG.Quasithin.Chapter15.Section01
