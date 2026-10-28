module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryCatalogue
public import Theory.SpecificGroups.Janko4.Model.IrreducibleCentralizer
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.SpecificGroups.Janko4.Model.Center
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.LocalA5Shape
public import Theory.SpecificGroups.Rudvalis.BinaryThreeFixer

/-!
# The genuine symplectic survivor before ordinary normalizer identification

Relative normality of K and the original intermediate-core identities show
that the full moved module centralizes the core of the local-Sylow supplement.
This excludes the extraspecial-core involution centralizer in J₄; its other
centralizer has insufficient two-part. In Rudvalis, the original field degree
is two or three: the local core-center bound excludes the first, and the
actual involutory fixer excludes the second.

The final theorem proves an actual nonbinary symplectic central quotient from
OutsideChoice, without assuming H = N_G(K). The configuration and Chapter 12
applications in RankOneModuleGenericGlobalLocalUniquenessCatalogue use this
result to restrict the remaining normalizer input to precisely that survivor.
Final discharge remains with qt-d-1222-rankone-global-uniqueness; the independent
nonblock producer retains its own branch.
Source: Aschbacher–Smith C.3.1, pp.149–151, and 4.3.3–6, pp.613–615.
The model arguments extend OrdinaryRecognitionJankoFour/Rudvalis to the earlier
source boundary and retain the intrinsic model files' ATLAS attribution.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (c : OutsideChoice T L) (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (K : Subgroup c.H) (ho : IsComponent c.H K)
  (hLK : L ≤ K.map c.H.subtype)
  (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
include D h ho hLK hout hKN
open ChapterA.Section02 ChapterA.Section03.SourceEmbeddings FiveLocalFF ClassificationModels

omit ho in
private theorem original_join_core
     :
    (((c.ordinaryLocal K) ⊔ (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K).pCoreIn 2).map
      (c.H.subtype.comp K.subtype) ≤ c.intermediate.pCoreIn 2 := by
  have hHN : c.H ≤ normalizer (K.map c.H.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hKN
  have hLI : L ≤ c.intermediate := le_sup_left
  have hI : c.intermediate ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sup_le_sup_left inf_le_left L
  have hIH : c.intermediate ≤ c.H := sup_le c.contains inf_le_right
  have hmax := fun J hIJ hJ => c.intermediate_maximal D h (J := J) hIJ hJ
  have hHout : ¬ c.H ≤ normalizer (L : Set G) :=
    fun hh => hout ((map_subtype_le K).trans hh)
  obtain ⟨hRS,hRJ⟩ := selected_core_sylow D h hLI hI hmax c.maximal hIH hHout
  have hIe := (intermediate_core_identities D h hLI hI).1
  let S := (T : Subgroup G) ⊓ c.H
  let B0 := K.map c.H.subtype
  let g := c.H.subtype.comp K.subtype
  have hg : Function.Injective g := c.H.subtype_injective.comp K.subtype_injective
  have hl : (c.ordinaryLocal K).map g = L := by
    rw [←map_map,map_subgroupOf_eq_of_le (c.ordinaryLocal_le hLK),
      map_subgroupOf_eq_of_le c.contains]
  have hs : ((((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K).map g = S ⊓ B0 := by
    rw [←map_map,subgroupOf_map_subtype,Subgroup.map_inf _ _ _ c.H.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right]
  have hSN : S ≤ normalizer (L : Set G) := inf_le_left.trans D.sylow_normalizes_component
  have hSK : S ≤ normalizer (S ⊓ B0 : Set G) :=
    (le_inf S.le_normalizer (inf_le_right.trans hHN)).trans
      inf_normalizer_le_normalizer_inf
  have hNJ : L ⊔ S ≤ normalizer ((L ⊔ S ⊓ B0 : Subgroup G) : Set G) := by
    apply sup_le (le_sup_left.trans (L ⊔ S ⊓ B0).le_normalizer)
    exact (le_inf hSN hSK).trans (L.normalizer_inf_normalizer_le_normalizer_sup (S ⊓ B0))
  have hR : c.intermediate.pCoreIn 2 ≤ S := hRS.le.trans inf_le_left
  have hj : c.intermediate ⊔ S = L ⊔ S := by
    rw [hIe,sup_assoc,sup_eq_right.mpr hR]
  rw [map_pCoreIn_of_injective 2 _ g hg,Subgroup.map_sup,hl,hs,hRJ,hj]
  exact pCoreIn_mono_of_normalizes (sup_le_sup_left inf_le_left L) hNJ

omit ho in
private theorem original_module_core_central
     :
    ((c.ordinaryModule.subgroupOf c.H).subgroupOf K) ≤
      centralizer (((c.ordinaryLocal K) ⊔ (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K).pCoreIn 2 : Set K) := by
  intro w hw q hq
  obtain ⟨z,hz,he⟩ := (c.c28 D h).module_le_center_radical hw
  have hqR := c.original_join_core D h K hLK hout hKN (mem_map_of_mem (c.H.subtype.comp K.subtype) hq)
  have hh := congrArg (fun a : c.intermediate.pCoreIn 2 => (a : G))
    (mem_center_iff.mp hz ⟨((q : c.H) : G),hqR⟩)
  apply Subtype.ext
  apply Subtype.ext
  change (q : G) * (w : G) = (w : G) * (q : G)
  change (q : G) * (z : G) = (z : G) * (q : G) at hh
  change (z : G) = (w : G) at he
  rwa [he] at hh

/-- The literal full module centralizes the core of the local-Sylow supplement. -/
theorem ordinary_model_module_centralizes_supplement_core
    {J : Type*} [Group J] [Finite J] (e : (K ⧸ center K) ≃* J) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    ((c.ordinaryModule.subgroupOf c.H).subgroupOf K).map f ≤
      centralizer ((((c.ordinaryLocal K) ⊔ (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K).map f).pCoreIn 2 : Set J) := by
  let := ho.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : f.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := by
    rw [hk,IsQuasisimple.center_eq_pCore (ho.1.pPrimeCore_eq_bot (c.c28 D h).oddCore_eq_bot)]
    exact pCore_isPGroup
  dsimp only
  rw [←map_pCoreIn_of_ker_isPGroup f hp]
  exact (map_mono (c.original_module_core_central D h K hLK hout hKN)).trans (map_centralizer_le_centralizer_image _ _)
omit c D h K ho hLK hout hKN in
private theorem small_core_center_central {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (center (pCore 2 A)) ≤ 2) :
    (center (pCore 2 A)).map (pCore 2 A).subtype ≤ center A := by
  let Z := (center (pCore 2 A)).map (pCore 2 A).subtype
  have hz : Nat.card Z ≤ 2 := by rwa [card_map_of_injective (pCore 2 A).subtype_injective]
  let : Z.Normal := by infer_instance
  by_cases h1 : Nat.card Z = 1
  · exact (card_eq_one.mp h1).le.trans bot_le
  · exact central_of_normal_card_two Z (by have := Nat.card_pos (α := Z); omega)

/-- The original module excludes an overgroup with a self-centralizing two-core
and core center of order at most two. -/
theorem ordinary_no_small_core_center_overgroup
    {J : Type*} [Group J] [Finite J] (e : (K ⧸ center K) ≃* J)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K)
    (X : Subgroup J)
    (hBX : (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) ≤ X)
    (hSX : (P : Subgroup K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) ≤ X)
    (hC : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hsmall : Nat.card (center (pCore 2 X)) ≤ 2) : False := by
  let := ho.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  let WK := (c.ordinaryModule.subgroupOf c.H).subgroupOf K
  let E := WK.map f
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  change B ≤ X at hBX
  change (S : Subgroup J) ≤ X at hSX
  have hEB : E ≤ B := map_mono (subgroupOf_mono K (subgroupOf_mono c.H
    (by simpa only [c.ordinary_span_eq] using (c.c28 D h).module_le)))
  have hEX := hEB.trans hBX
  have hQS : X.pCoreIn 2 ≤ (S : Subgroup J) := by
    have hh := pCoreIn_le_sylow X (S.subtype hSX)
    change X.pCoreIn 2 ≤ ((S : Subgroup J).subgroupOf X).map X.subtype at hh
    rwa [map_subgroupOf_eq_of_le hSX] at hh
  have hQB : X.pCoreIn 2 ≤ (B ⊔ (S : Subgroup J)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) (hQS.trans le_sup_right)
      ((sup_le hBX hSX).trans (X.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hEC : E ≤ centralizer (X.pCoreIn 2 : Set J) := by
    have hh := c.ordinary_model_module_centralizes_supplement_core D h K ho hLK hout hKN e
    dsimp only at hh
    rw [Subgroup.map_sup,←hP] at hh
    exact hh.trans (centralizer_le hQB)
  have hEQ : E ≤ X.pCoreIn 2 := by
    intro w hw
    have hh : (⟨w,hEX hw⟩ : X) ∈ centralizer (pCore 2 X : Set X) := by
      intro q hq
      exact Subtype.ext (hEC hw q (mem_map_of_mem X.subtype hq))
    exact mem_map_of_mem X.subtype (hC hh)
  have hEZ : E ≤ (center (pCore 2 X)).map (X.subtype.comp (pCore 2 X).subtype) := by
    intro w hw
    obtain ⟨q,hq,he⟩ := hEQ hw
    refine ⟨⟨q,hq⟩,mem_center_iff.mpr ?_,he⟩
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change (r : J) * (q : J) = (q : J) * (r : J)
    change (q : J) = w at he
    rw [he]
    exact hEC hw r (mem_map_of_mem X.subtype r.property)
  have hEcenter : E ≤ (center X).map X.subtype := by
    apply hEZ.trans
    rw [←map_map]
    exact map_mono (small_core_center_central hsmall)
  have hECb : E ≤ centralizer (B : Set J) := by
    rintro w hw b hb
    obtain ⟨z,hz,rfl⟩ := hEcenter hw
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hBX hb⟩)
  have hWL : c.ordinaryModule ≤ L := by simpa only [c.ordinary_span_eq] using (c.c28 D h).module_le
  have hWH := hWL.trans c.contains
  have hWK : c.ordinaryModule.subgroupOf c.H ≤ K :=
    (subgroupOf_mono c.H hWL).trans (c.ordinaryLocal_le hLK)
  have hmK : ⁅WK,(c.ordinaryLocal K)⁆ = WK := by
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le (c.ordinaryLocal_le hLK)]
    apply map_injective c.H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le
      c.contains]
    simpa only [c.ordinary_span_eq] using (c.c28 D h).module_commutator.symm
  have hm : ⁅E,B⁆ = E := by rw [←map_commutator,hmK]
  have he : E = ⊥ := hm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hECb)
  have hk : f.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hz : WK ≤ center K := hk ▸ (map_eq_bot_iff WK).mp he
  apply (c.c28 D h).ordinary_module_not_centralizes K ho
  intro w hw k hk
  exact congrArg (fun x : K => (x : c.H))
    (mem_center_iff.mp (hz (show (⟨w,hWK hw⟩ : K) ∈ WK from hw)) ⟨k,hk⟩)

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original full module, Sylow and R₀ action exclude the J₄ central quotient. -/
theorem ordinary_no_jankoFour
    {n : ℕ} (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Janko4.Model) : False := by
  let := ho.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  obtain ⟨P,hP,_,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hSB : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set _) := by
    apply (map_mono ?_).trans ((c.ordinaryLocal K).le_normalizer_map f)
    rw [hP]
    exact (c.ordinary_component_sylow_normalizes_local D K)
  obtain ⟨a,ha,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e
  obtain ⟨g,hg⟩ := Janko4.AdequateLocal.exists_eq_conj a
  obtain ⟨x,hx,he,_⟩ := MulAut.inner_involution_representative Janko4.model_center_eq_bot
    a ha ⟨g,hg⟩
  have hxc : x ∈ centralizer (B : Set Janko4.Model) := by
    intro b hb
    have hh := hfix b hb
    rw [he,MulAut.conj_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have heven : 2 ∣ Nat.card (centralizer (B : Set Janko4.Model)) := by
    simpa only [Subgroup.orderOf_mk,hx] using
      orderOf_dvd_natCard (⟨x,hxc⟩ : centralizer (B : Set Janko4.Model))
  obtain ⟨z,hz,hzBS⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup Janko4.Model) S.isPGroup' hSB heven
  let X := centralizer ({z} : Set Janko4.Model)
  have hBX : B ≤ X := le_sup_left.trans hzBS
  have hSX : (S : Subgroup Janko4.Model) ≤ X := le_sup_right.trans hzBS
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with hb | hb
  · obtain ⟨b⟩ := hb
    apply c.ordinary_no_small_core_center_overgroup D h K ho hLK hout hKN e P hP X hBX hSX
      (Janko4.InvolutionCentralizers.centralizer_characteristic_two z hz)
    let bP := (b.subgroupMap (pCore 2 X)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 b))
    rw [Nat.card_congr (centerCongr bP).toEquiv]
    let := Janko4.InvolutionCentralizers.First.centralizer_twoCore_extraspecial
    exact (IsExtraspecial.center_order_p 2
      (pCore 2 Janko4.InvolutionCentralizers.First.centralizer)).le
  · obtain ⟨b⟩ := hb
    have hdiv : 2^21 ∣ Nat.card S := by
      have hd : 2^21 ∣ Nat.card Janko4.Model := by rw [Janko4.Cardinality.model_card]; norm_num
      rw [←(S : Subgroup Janko4.Model).card_mul_index] at hd
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index).pow_left 21
        |>.dvd_of_dvd_mul_right hd
    have hd := hdiv.trans (card_dvd_of_le hSX)
    rw [Nat.card_congr b.toEquiv,Janko4.InvolutionCentralizers.Second.ambient_card] at hd
    norm_num at hd
omit c D h K ho hLK hout hKN in
private theorem core_center_small {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (center (pCore 2 A)) ≤ 2) :
    (center (pCore 2 A)).map (pCore 2 A).subtype ≤ center A := by
  let Z := (center (pCore 2 A)).map (pCore 2 A).subtype
  have hz : Nat.card Z ≤ 2 := by rwa [card_map_of_injective (pCore 2 A).subtype_injective]
  let : Z.Normal := by infer_instance
  by_cases h1 : Nat.card Z = 1
  · exact (card_eq_one.mp h1).le.trans bot_le
  · exact central_of_normal_card_two Z (by have := Nat.card_pos (α := Z); omega)

/-- The original local quotient and full Sylow exclude the Rudvalis central quotient. -/
theorem ordinary_no_rudvalis
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Rudvalis.Model) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  have hd := c.ordinary_model_moved_order_dvd D h K ho hLK hout hKN hn hpsl e
  rw [Rudvalis.model_card] at hd
  have hn5 : n < 5 := by
    by_contra! hh
    have h := (pow_dvd_pow 2 (by omega : 15 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd)
    norm_num at h
  have hcases : n = 2 ∨ n = 3 := by
    by_cases h4 : n = 4
    · subst n; norm_num at hd
    · omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
    obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    obtain ⟨P,hP,_,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hSN : (S : Subgroup Rudvalis.Model) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans ((c.ordinaryLocal K).le_normalizer_map f)
      rw [hP]
      exact (c.ordinary_component_sylow_normalizes_local D K)
    exact c.ordinary_model_core_center_not_central D h K ho hLK e (core_center_small
      (MainConverse.SporadicLocal.RuEven.normalized_a5_core_center_card_le_two S B hSN (b.trans d)))
  · let := ho.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : IsSimpleGroup Rudvalis.Model := e.isSimpleGroup_congr.mp inferInstance
    obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e
    have h21 : 21 ∣ Nat.card B := (by decide : 21 ∣ 2^3*((2^3)^2-1)).trans
      (c.ordinary_model_local_order_dvd D h K ho hLK e hpsl)
    have he := Rudvalis.eq_one_of_fixes_twentyOne B h21 r
      (hr ▸ pow_orderOf_eq_one r) hfix
    simp only [he,orderOf_one] at hr
    omega
/-- Every raw ordinary source choice has an actual nonbinary symplectic central quotient.
The normalizer equality has not been used in any row exclusion. -/
theorem ordinary_symplectic_quotient
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    ∃ m : ℕ, 1 < m ∧ IsPSp (K ⧸ center K) 2 (2 ^ m) := by
  rcases c.ordinary_symplectic_or_jankoFour_or_rudvalis D h K ho hLK hout hKN hn hpsl with
    hm | hj | hr
  · exact hm
  · exact (c.ordinary_no_jankoFour D h K ho hLK hout hKN hpsl hj.some).elim
  · exact (c.ordinary_no_rudvalis D h K ho hLK hout hKN hn hpsl hr.some).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
