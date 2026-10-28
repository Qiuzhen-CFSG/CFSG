module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalFiniteCarriers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalFiniteCarriers
public import CFSG.Quasithin.ChapterF.Section01.RankOneHigmanSimsLocal
public import CFSG.Quasithin.ChapterF.Section01.RankOneRudvalisLocal
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoTwoResidual
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFour

/-!
# The original residual in Higman–Sims and Rudvalis containers

The full-Sylow local covers in these two models have quotient sections of
order dividing 840. Apply their literal quotient maps to the image of the
original residual in C/O₂(C). Escape makes that image proper: equality
would make it normal in Y/O₂(Y), and the original two-core lifting theorem
would force normalization upstairs. Thus this restriction does not assume
that the selected seed is the residual.

The resulting order bound excludes a moved A₅ pair, whose residual has
two factors of five. The original E.2.2 alternatives then force a rank-one
quotient. Its small two-part leaves PSL₂(4) or PSL₂(8), and the factor nine
excludes PSL₂(8). The original right Hall subgroup consequently has order
three. All equivalences retain the possible two-group kernels.

These are source reductions on the same selected component, used by the
remaining-carrier assembly and its literal Chapter12 application. The
escaping-action exclusions for HS and Rudvalis are still required; no
SourceLocalCartanEscape inhabitant is asserted. Internal imports reuse
this proof family's checked transport and finite-order lemmas.
Source: Aschbacher–Smith A.3.12(18,20), E.2.2 and 5.1.12–13,
printed pp.47–48,215–216,635–638, refs/quasithin.pdf. The native
carrier calculations retain their ATLAS attribution and LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem residual_section_dvd_of_model
    {T : Sylow 2 G} {L W H A Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    {X : Type*} [Group X] [Finite X] (eModel : (C ⧸ pCore 2 C) ≃* X)
    (hbound : ∀ (S : Sylow 2 X) (J R : Subgroup X), (S : Subgroup X) ≤ J →
      J ≠ ⊤ → R ≤ J → Nat.card (R ⧸ pCore 2 R) ∣ 840) :
    Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 840 := by
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let : Cbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal Cbar
  let U := Rbar.subgroupOf Cbar
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnU : (Q : Subgroup Cbar) ≤ normalizer (U : Set Cbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hle]
    exact comap_mono hn
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := (subgroupOfEquivOfLe hle).symm
  let eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (U ⧸ pCore 2 U) :=
    (QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).trans
      (e₂.trans (QuotientGroup.congr _ _ e₃ (pCore_map_iso 2 e₃)))
  let eC : Cbar ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hC).symm
  let e := eC.trans eModel
  let V := U.map e.toMonoidHom
  let S' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let v := e.subgroupMap U
  let eV := QuotientGroup.congr _ _ v (pCore_map_iso 2 v)
  have hu : U ≠ ⊤ := by
    intro he
    have heq : Rbar = Cbar := le_antisymm hle (subgroupOf_eq_top.mp he)
    apply hescape
    apply (residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp
    change (A.subgroupOf Y).map q ≤ normalizer (Rbar : Set _)
    rw [heq, normalizer_eq_top]
    exact le_top
  have hv : V ≠ ⊤ := by
    intro he
    apply hu
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact he
  have hvn : (S' : Subgroup X) ≤ normalizer (V : Set X) :=
    (map_mono (f := e.toMonoidHom) hnU).trans (le_normalizer_map _)
  let : Group.IsPerfect Cbar := (hC.map_quotient (pCore 2 Y)).perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hJ := proper_normalized_join S' V hv hvn
  rw [Nat.card_congr (eR.trans eV).toEquiv]
  exact hbound S' _ V le_sup_right hJ le_sup_left

/-- The original residual section in either remaining sparse sporadic
container has order dividing 840; no fixed-seed premise is used. -/
theorem higmanSims_rudvalis_residual_order
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model)) :
    Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 840 := by
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective]
      using (inferInstance : C.Normal)
  have hRC : residual H ≤ C.map Y.subtype := by
    rw [←horbit]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hKC
      (hH.1.1.2.trans (hY.2.trans hYn))
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact residual_section_dvd_of_model h hH hgen hY hescape C hC hRC e
      Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_section_order
  · obtain ⟨e⟩ := hm
    have hO : pCore 2 Rudvalis.Model = ⊥ := by
      rw [←pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
    exact residual_section_dvd_of_model h hH hgen hY hescape C hC hRC e
      (Rudvalis.SylowOvergroups.proper_overgroup_section_order
        (ChapterF.Source.RudvalisLocal.sylow_overgroup_cover hO))

private theorem seed_eq_residual_of_small_section
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hbound : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 840) :
    K = residual H := by
  by_contra hmoved
  have hm := moved_seed_linear_four_of_escape hG hK hKT horbit hmoved hY hescape
  have hmove : K < conjugateSpanBy K (T : Subgroup G) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    change K < componentOrbit K (T : Subgroup G)
    exact lt_of_le_of_ne (le_componentOrbit K _) (fun he => hmoved (he.trans horbit))
  have hrad := Chapter1.Section02.MovedMaximality.moved_local_radical_eq_core hG T hK hmove
  have hKR : K ≤ residual H := horbit ▸ le_componentOrbit K (T : Subgroup G)
  have hTR : (T : Subgroup G) ≤ normalizer (residual H : Set G) :=
    (show (T : Subgroup G) ≤ H by rw [←hKT]; exact le_sup_right).trans (le_normalizer_residual H)
  have hd := Chapter1.Section02.MovedMaximality.actual_pair_square_dvd T hK.1 hKR hTR hmove
  rw [hrad] at hd
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hcard : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr (e.trans e5).toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  rw [hcard] at hd
  let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hb : Nat.card (residual H ⧸ pCore 2 (residual H)) ∣ 840 := by
    rwa [←Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv]
  have hh := hd.trans ((radical_quotient_card_dvd_twoCore (residual H)).trans hb)
  norm_num at hh

/-- Both sparse sporadic rows force the same selected seed to be the whole
residual, its literal quotient to be PSL₂(4), and the original right Hall
subgroup to have order three. -/
theorem higmanSims_rudvalis_residual_and_hall
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model)) :
    K = residual H ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      Nat.card B = 3 := by
  have hd := higmanSims_rudvalis_residual_order h hH hgen horbit hY hescape C hC hKC hm
  have he := seed_eq_residual_of_small_section h.qtke hK hKT horbit hY hescape hd
  have hR : (pResidual 2 H).IsCComponent := by
    have hh := (he ▸ hK).1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hrank := residual_rankOne_of_order h hH hgen hY hescape hR (.inl rfl)
    (hd.trans (by decide : 840 ∣ 20160))
  have hns : ¬ Group.IsSolvable ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 (pResidual 2 H)) := pCore_isNilpotent
    exact hR.not_isSolvable (Group.isSolvable_of_ker_le_range
      (pCore 2 (pResidual 2 H)).subtype (QuotientGroup.mk' (pCore 2 (pResidual 2 H))) (by simp))
  obtain ⟨f,hf,hf3,hmodel⟩ := hrank.binary_of_small_twoPart hns
    (fun h16 => (by decide : ¬ 16 ∣ 840) (h16.trans hd))
  have hf2 : f = 2 := by
    by_contra hne2
    have hf3 : f = 3 := by omega
    subst f
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1),mul_one,hF,←Nat.card_congr e.toEquiv] at hc
    rw [hc] at hd
    norm_num at hd
  subst f
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hmodel
    exact ⟨eq.symm.trans (b.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact ⟨he,hmodel,right_hall_card_three_of_residual_A5 h hH hgen c hA5⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
