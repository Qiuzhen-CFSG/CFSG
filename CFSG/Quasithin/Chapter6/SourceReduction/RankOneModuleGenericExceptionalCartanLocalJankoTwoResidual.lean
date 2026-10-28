module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoTwoAction
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.PairedHall
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.ContainingQuotients
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.RightHall
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.LinearExclusion
public import CFSG.Quasithin.ChapterF.Section01.RankOneJankoTwoLocal
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers

/-!
# The original residual in the Hall--Janko containing row

The already constructed escaping cubic rules out the moved A₅ seed by the
ambient three-rank bound. Thus the same seed is the entire original residual.
Restrict its actual image to C/O₂(C), with the full Sylow intersection.
The native J₂ overgroup orders bound the residual section order; the source
E.2.2 alternatives then leave a rank-one model. The proper rank-one local
calculation identifies its literal quotient as PSL₂(4). The original right
Hall subgroup consequently has order three.

No residual marking, degree two or chosen-module coordinates are assumed.
Both Hall conditions and the intrinsic two-cores are preserved. Exhaustive
container selection and the binary-triality exclusion remain separate duties.
Source: Aschbacher--Smith 5.1.10--13, printed pp.634--637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
private theorem proper_normalized_join {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (S : Sylow 2 X) (R : Subgroup X) (hr : R ≠ ⊤)
    (hn : (S : Subgroup X) ≤ normalizer (R : Set X)) : R ⊔ (S : Subgroup X) ≠ ⊤ := by
  intro he
  let : R.Normal := normalizer_eq_top_iff.mp (top_unique (he ▸ sup_le R.le_normalizer hn))
  let : Nontrivial (X ⧸ R) := QuotientGroup.nontrivial_iff.mpr hr
  let : Group.IsPerfect (X ⧸ R) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective R)
  let : Group.IsNilpotent (X ⧸ R) :=
    (isPGroup_quotient_of_sup_eq_top R (S : Subgroup X) S.isPGroup' he).isNilpotent
  exact Group.IsPerfect.not_isSolvable (X ⧸ R) inferInstance

/-- The original residual has literal PSL₂(4) quotient in the J₂
row, retaining its possible two-core throughout the quotient restriction. -/
theorem residual_section_of_janko_two
    {T : Sylow 2 G} {L W H A Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent)
    (hRC : residual H ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 := by
  have hR' : (pResidual 2 H).IsCComponent := by
    have hh := hR.1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlq hle (hC.map_quotient (pCore 2 Y)).subnormal
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
  let e := eC.trans hm.some
  let V := U.map e.toMonoidHom
  let S' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let v := e.subgroupMap U
  let eV := QuotientGroup.congr _ _ v (pCore_map_iso 2 v)
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (hH.1.1.2.trans (le_normalizer_residual H))) (le_componentOrbit _ _)
  have hlt := seed_image_lt_container h.qtke (map_subtype_le _) hH.1.1.2
    hR ho hY hescape C hC hRC
  have hu : U ≠ ⊤ := fun he => hlt.not_ge (subgroupOf_eq_top.mp he)
  have hv : V ≠ ⊤ := by
    intro he
    apply hu
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact he
  have hvn : (S' : Subgroup Sporadic.LeechRelated.J2.Carrier) ≤ normalizer (V : Set _) :=
    (map_mono (f := e.toMonoidHom) hnU).trans (le_normalizer_map _)
  let : Group.IsPerfect Cbar := (hC.map_quotient (pCore 2 Y)).perfect
  let : Group.IsPerfect Sporadic.LeechRelated.J2.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hJ : V ⊔ (S' : Subgroup Sporadic.LeechRelated.J2.Carrier) ≠ ⊤ :=
    proper_normalized_join S' V hv hvn
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 5760 := by
    rw [Nat.card_congr (eR.trans eV).toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 V)).trans
      (card_dvd_of_le (show V ≤ V ⊔ (S' : Subgroup _) from le_sup_left))
    rcases Sporadic.LeechRelated.J2.SylowOvergroups.proper_overgroup_order
      S' _ le_sup_right hJ with h | h
    · exact hh.trans (h.trans (by decide))
    · exact hh.trans (h.trans (by decide))
  have hmodel : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hgen with hs | hs
    · obtain ⟨K,f,hK,hqs,_,_,hc | hc⟩ := hs
      · have hKR : K = pResidual 2 H := by
          apply hK.eq_of_le hR'
          let := hK.perfect
          apply le_sInf
          rintro N ⟨hn,hN⟩
          let := hn
          let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
          exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
        subst K
        obtain ⟨t,_,hne,_⟩ := hc.1.exchanged_product
        exact (hne (mem_normalizer_iff_map_conj_eq.mp
          (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
            rw [normalizer_eq_top]; exact mem_top _)).symm).elim
      · have he : K = pResidual 2 H :=
          BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hK
        subst K
        have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
          apply normal_le_normalCore.mpr
          exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
            (comap_mono h.sylow_normalizes)
        exact Prime.single_bender_component_quotient hK hqs hO hc.1 hc.2
    · obtain ⟨K,f,hK,hqs,_,hf,hc,hm⟩ := hs
      have hmodels := Prime.diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hK hqs hc hf hm
      have hf2 := Prime.diagram_finite_order hf (by simp [Prime.finiteOrders])
        (hd.trans (by decide : 5760 ∣ 604800)) hmodels
      subst f
      rcases hmodels with hlin | hsl | hsp
      · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsl
        rw [Nat.card_congr a.toEquiv,
          Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hd
        norm_num at hd
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
          (by simpa only [Nat.card_eq_fintype_card] using hF)
        let b := a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
        rw [Nat.card_congr b.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
        norm_num at hd
  have hns : ¬ Group.IsSolvable V := by
    intro hs
    let := hs
    let : Group.IsSolvable (V ⧸ pCore 2 V) := inferInstance
    let d : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (V ⧸ pCore 2 V) := eR.trans eV
    let : Group.IsSolvable ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
      Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom) d.injective
    let : Group.IsNilpotent (pCore 2 (pResidual 2 H)) := pCore_isNilpotent
    exact hR'.not_isSolvable (Group.isSolvable_of_ker_le_range
      (pCore 2 (pResidual 2 H)).subtype
      (QuotientGroup.mk' (pCore 2 (pResidual 2 H))) (by simp))
  exact (ChapterF.Source.JankoTwoLocal.rankOne_quotient_four S' V hv hns hvn
    (hmodel.of_equiv (eR.trans eV).symm)).of_mulEquiv (eR.trans eV)


/-- The original escaping cubic excludes a moved seed. The actual J₂ local
geometry then identifies its residual quotient and the original right Hall. -/
theorem normal_janko_two_residual_and_hall
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    K = residual H ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      Nat.card B = 3 := by
  have hYn : Y ≤ normalizer (C.map Y.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le C)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective]
      using (inferInstance : C.Normal)
  have hRX : residual H ≤ C.map Y.subtype := by
    rw [←horbit]
    exact iSup_conjugates_le_of_le_normalizer _ _ _ hKC
      (hH.1.1.2.trans (hY.2.trans hYn))
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRX
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  obtain ⟨D,hD,hDc,hDn⟩ := janko_two_escaping_cubic h hH hgen c hY hescape C hC hRC hm
  have hKR := escape_seed_eq_residual_of_cubic h hH hgen c hKH hK hqs
    hKT hKL horbit hY hescape (hD.trans inf_le_left) hDc hDn
  have hfour := residual_section_of_janko_two h hH hgen hY hescape
    (hKR ▸ hKL) C hC hRX hm
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hfour
    exact ⟨eq.symm.trans (b.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact ⟨hKR,hfour,right_hall_card_three_of_residual_A5 h hH hgen c hA5⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
