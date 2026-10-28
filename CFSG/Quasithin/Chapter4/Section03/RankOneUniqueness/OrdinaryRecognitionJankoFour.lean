module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionModule
public import Theory.SpecificGroups.Janko4.Model.IrreducibleCentralizer
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.SpecificGroups.Janko4.Model.Center

/-!
# The last J₄ row in ordinary rank-one recognition

The full source module centralizes the two-core of the original local subgroup
joined with the component Sylow. Consequently an overgroup of their model
images cannot have a self-centralizing two-core whose center has order at most
two: that would centralize the fully moved module and force its image to vanish.

For J₄ the original R₀ action is inner and gives an involution centralizing the
local subgroup. The full Sylow normalizes that subgroup, so the pair lies in
an involution centralizer. The first centralizer has an extraspecial two-core
and is excluded by the preceding argument; the second has insufficient two-part
to contain the full Sylow. All subgroup and module images are the literal ones.

Source: Aschbacher--Smith C.3.1(6), pp.149--151, and 4.3.6, p.614;
the intrinsic J₄ centralizer calculations retain their ATLAS attribution.
-/

public section

open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem original_join_core (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((c.ordinaryLocal ⊔ c.ordinarySylowInH.subgroupOf c.K).pCoreIn 2).map
      (c.H.subtype.comp c.K.subtype) ≤ c.I.pCoreIn 2 := by
  let S := (T : Subgroup G) ⊓ c.H
  let K := c.K.map c.H.subtype
  let g := c.H.subtype.comp c.K.subtype
  have hg : Function.Injective g := c.H.subtype_injective.comp c.K.subtype_injective
  have hl : c.ordinaryLocal.map g = L := by
    rw [←map_map,map_subgroupOf_eq_of_le c.ordinaryLocal_le,
      map_subgroupOf_eq_of_le (c.le_I.trans c.I_le_H)]
  have hs : (c.ordinarySylowInH.subgroupOf c.K).map g = S ⊓ K := by
    rw [←map_map,subgroupOf_map_subtype,Subgroup.map_inf _ _ _ c.H.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right]
  have hSN : S ≤ normalizer (L : Set G) := inf_le_left.trans D.sylow_normalizes_component
  have hSK : S ≤ normalizer (S ⊓ K : Set G) :=
    (le_inf S.le_normalizer (inf_le_right.trans c.normalizer_component.le)).trans
      inf_normalizer_le_normalizer_inf
  have hNJ : L ⊔ S ≤ normalizer ((L ⊔ S ⊓ K : Subgroup G) : Set G) := by
    apply sup_le (le_sup_left.trans (L ⊔ S ⊓ K).le_normalizer)
    exact (le_inf hSN hSK).trans (L.normalizer_inf_normalizer_le_normalizer_sup (S ⊓ K))
  have hR : c.I.pCoreIn 2 ≤ S := c.core_sylow.le.trans inf_le_left
  have hj : c.I ⊔ S = L ⊔ S := by
    rw [c.I_eq,sup_assoc,sup_eq_right.mpr hR]
  rw [map_pCoreIn_of_injective 2 _ g hg,Subgroup.map_sup,hl,hs,c.core_join,hj]
  exact pCoreIn_mono_of_normalizes (sup_le_sup_left inf_le_left L) hNJ

private theorem original_module_core_central (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    ((c.ordinaryModule.subgroupOf c.H).subgroupOf c.K) ≤
      centralizer ((c.ordinaryLocal ⊔ c.ordinarySylowInH.subgroupOf c.K).pCoreIn 2 : Set c.K) := by
  intro w hw q hq
  obtain ⟨z,hz,he⟩ := c.c28.module_le_center_radical hw
  have hqR := c.original_join_core D (mem_map_of_mem (c.H.subtype.comp c.K.subtype) hq)
  have hh := congrArg (fun a : c.I.pCoreIn 2 => (a : G))
    (mem_center_iff.mp hz ⟨((q : c.H) : G),hqR⟩)
  apply Subtype.ext
  apply Subtype.ext
  change (q : G) * (w : G) = (w : G) * (q : G)
  change (q : G) * (z : G) = (z : G) * (q : G) at hh
  change (z : G) = (w : G) at he
  rwa [he] at hh

/-- The literal full module centralizes the core of the local-Sylow supplement. -/
theorem ordinary_model_module_centralizes_supplement_core (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {J : Type*} [Group J] [Finite J] (e : (c.K ⧸ center c.K) ≃* J) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
    ((c.ordinaryModule.subgroupOf c.H).subgroupOf c.K).map f ≤
      centralizer (((c.ordinaryLocal ⊔ c.ordinarySylowInH.subgroupOf c.K).map f).pCoreIn 2 : Set J) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  have hk : f.ker = center c.K := by
    ext x
    change e (QuotientGroup.mk' (center c.K) x) = 1 ↔ x ∈ center c.K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hp : IsPGroup 2 f.ker := by
    rw [hk,c.ordinary_center_eq_twoCore ho]
    exact pCore_isPGroup
  dsimp only
  rw [←map_pCoreIn_of_ker_isPGroup f hp]
  exact (map_mono (c.original_module_core_central D)).trans (map_centralizer_le_centralizer_image _ _)
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
theorem ordinary_no_small_core_center_overgroup (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {J : Type*} [Group J] [Finite J] (e : (c.K ⧸ center c.K) ≃* J)
    (P : Sylow 2 c.K) (hP : (P : Subgroup c.K) = c.ordinarySylowInH.subgroupOf c.K)
    (X : Subgroup J)
    (hBX : c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) ≤ X)
    (hSX : (P : Subgroup c.K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) ≤ X)
    (hC : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (hsmall : Nat.card (center (pCore 2 X)) ≤ 2) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  let WK := (c.ordinaryModule.subgroupOf c.H).subgroupOf c.K
  let E := WK.map f
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  change B ≤ X at hBX
  change (S : Subgroup J) ≤ X at hSX
  have hEB : E ≤ B := map_mono (subgroupOf_mono c.K (subgroupOf_mono c.H
    (by simpa only [c.ordinary_span_eq] using c.c28.module_le)))
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
    have hh := c.ordinary_model_module_centralizes_supplement_core D ho e
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
  have hWL : c.ordinaryModule ≤ L := by simpa only [c.ordinary_span_eq] using c.c28.module_le
  have hWH := hWL.trans (c.le_I.trans c.I_le_H)
  have hWK : c.ordinaryModule.subgroupOf c.H ≤ c.K :=
    (subgroupOf_mono c.H hWL).trans c.ordinaryLocal_le
  have hmK : ⁅WK,c.ordinaryLocal⁆ = WK := by
    apply map_injective c.K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le c.ordinaryLocal_le]
    apply map_injective c.H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le
      (c.le_I.trans c.I_le_H)]
    simpa only [c.ordinary_span_eq] using c.c28.module_commutator.symm
  have hm : ⁅E,B⁆ = E := by rw [←map_commutator,hmK]
  have he : E = ⊥ := hm.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hECb)
  have hk : f.ker = center c.K := by
    ext x
    change e (QuotientGroup.mk' (center c.K) x) = 1 ↔ x ∈ center c.K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hz : WK ≤ center c.K := hk ▸ (map_eq_bot_iff WK).mp he
  apply c.c28.ordinary_module_not_centralizes c.K ho
  intro w hw k hk
  exact congrArg (fun x : c.K => (x : c.H))
    (mem_center_iff.mp (hz (show (⟨w,hWK hw⟩ : c.K) ∈ WK from hw)) ⟨k,hk⟩)

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The original full module, Sylow and R₀ action exclude the J₄ central quotient. -/
theorem ordinary_no_jankoFour (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    (e : (c.K ⧸ center c.K) ≃* Janko4.Model) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  obtain ⟨P,hP,_,_⟩ := c.ordinary_model_local_data D ho e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hSB : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set _) := by
    apply (map_mono ?_).trans (c.ordinaryLocal.le_normalizer_map f)
    rw [hP]
    exact c.ordinary_component_sylow_normalizes_local D
  obtain ⟨a,ha,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
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
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup Janko4.Model) S.isPGroup' hSB heven
  let X := centralizer ({z} : Set Janko4.Model)
  have hBX : B ≤ X := le_sup_left.trans h
  have hSX : (S : Subgroup Janko4.Model) ≤ X := le_sup_right.trans h
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with hb | hb
  · obtain ⟨b⟩ := hb
    apply c.ordinary_no_small_core_center_overgroup D ho e P hP X hBX hSX
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

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
