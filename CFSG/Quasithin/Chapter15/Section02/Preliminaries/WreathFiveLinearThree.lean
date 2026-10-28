module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveRankOne
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.UnipotentOvergroups
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.SL2.PerfectImageCore
public import Theory.SpecificGroups.SL2.ResidualTwoExtension

/-!
# The linear-three case in the original marked-five wreath argument

Restrict the original local A₅ component to the actual full Sylow in L₁.
If the component and that Sylow generate the whole SL₃ quotient, lifting
through O₂(L₁) forces K=L₁, contradicting the quotient order sixty. Otherwise
Sylow conjugacy places the image in a standard point or line parabolic.
Perfectness puts it in the affine local subgroup. Its literal two-core
quotient is SL₂ over the same field, and full-Sylow local-component exhaustion
makes the projection surjective. The source two-core is killed by this
projection, so the SL₂ order divides sixty and the field degree is at most two.

The original H-star consumer retains the same K,Y,S,W,R,L₁ and combines this
with the rank-one exclusion. It excludes both linear models with field degree
divisible by four. Producing those models from the full C.2.7/A.3.15 comparison
remains separate; no classification or placement premise is added here.
Source: Aschbacher--Smith, original15.2.4, printed p.1107.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

omit [Finite X] in
private theorem rankOne_degree_of_surjective
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (f : X →* SL(2,F.Carrier)) (hf : Function.Surjective f) : F.degree ≤ 2 := by
  have hk := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker f
  let q := QuotientGroup.lift (pCore 2 X) f hk
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ f hf hk
  have hd : 2 ^ F.degree ∣ 60 := by
    have hh : 2 ^ F.degree ∣ Nat.card SL(2,F.Carrier) := by
      rw [GorensteinWalter.sl2_card_formula,F.card_eq]
      exact dvd_mul_right _ _
    exact hc ▸ hh.trans (card_dvd_of_surjective q hq)
  by_contra hn
  have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ F.degree)).trans hd
  norm_num at hh

private theorem rankOne_local_eq_top (F : BinaryField) (hF : 1 < F.degree)
    (P : Sylow 2 SL(2,F.Carrier)) (B : Subgroup SL(2,F.Carrier))
    (hB : B ∈ ChapterA.Section03.localCComponents P) : B = ⊤ := by
  have hlarge : 3 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    omega
  let : IsQuasisimple SL(2,F.Carrier) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge (.refl _)
  have ht : (⊤ : Subgroup SL(2,F.Carrier)).IsCComponent :=
    (show IsComponent SL(2,F.Carrier) ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hj : B ⊔ (P : Subgroup SL(2,F.Carrier)) = ⊤ := by
    by_contra hn
    let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup P _ le_sup_right hn
    exact hB.not_isSolvable inferInstance
  change (B.subgroupOf (B ⊔ (P : Subgroup SL(2,F.Carrier)))).IsCComponent at hB
  rw [hj] at hB
  have hc : B.IsCComponent := by
    have h := hB.map_subtype (show (⊤ : Subgroup SL(2,F.Carrier)).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact hc.eq_of_le ht le_top

omit [Finite X] in
private theorem degree_of_local_projection
    {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 A) (f : X →* A)
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (D : Subgroup A) (hBD : f.range ≤ D) (hPD : (P : Subgroup A) ≤ D)
    (q : D →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] : F.degree ≤ 2 := by
  by_contra hn
  have hF : 1 < F.degree := by omega
  let P₀ := P.subtype hPD
  have hl := ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hBD
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have he : (f.range.subgroupOf D).map q = ⊤ :=
    rankOne_local_eq_top F hF (P₀.mapSurjective hq) _ hl'
  let f₀ := f.codRestrict D (fun x => hBD ⟨x,rfl⟩)
  have hr : f₀.range = f.range.subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  have hs : Function.Surjective (q.comp f₀) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hr,he]
  exact hn (rankOne_degree_of_surjective hc F (q.comp f₀) hs)

omit [Finite X] in
private theorem degree_of_proper_linearThree_join
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 SL(3,F.Carrier)) (f : X →* SL(3,F.Carrier))
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (hproper : f.range ⊔ (P : Subgroup SL(3,F.Carrier)) ≠ ⊤) : F.degree ≤ 2 := by
  by_contra hn
  have hcard : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  let U := Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow
    F.Carrier F.degree_pos F.card_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F.Carrier) P U
  let a := MulAut.conj g
  let f' := a.toMonoidHom.comp f
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP : (P : Subgroup SL(3,F.Carrier)).map a.toMonoidHom =
      Matrix.PSL3.LinearThree.unipotentSL F.Carrier := congrArg Sylow.toSubgroup hg
  have hP' : (P' : Subgroup SL(3,F.Carrier)) =
      Matrix.PSL3.LinearThree.unipotentSL F.Carrier := hP
  let : Group.IsSolvable a.toMonoidHom.ker := by
    have he : a.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff a.toMonoidHom).mpr a.injective
    rw [he]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal a.toMonoidHom
  have hl' : f'.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hP',←hP]
    simpa only [f',MonoidHom.range_comp] using hl
  have hj : f'.range ⊔ (P' : Subgroup SL(3,F.Carrier)) ≠ ⊤ := by
    intro hh
    apply hproper
    apply (map_injective (f := a.toMonoidHom) a.injective)
    dsimp only [f'] at hh
    rw [MonoidHom.range_comp,hP',←hP] at hh
    simpa only [Subgroup.map_sup,map_top_of_surjective a.toMonoidHom a.surjective,
      MonoidHom.range_comp] using hh
  have hp := Matrix.PSL3.LinearThree.UnipotentOvergroups.overgroup_unipotentSL F.Carrier
    (f'.range ⊔ (P' : Subgroup SL(3,F.Carrier))) (hP' ▸ le_sup_right) hj
  let : Group.IsPerfect f'.range := Group.IsPerfect.range f'
  rcases hp with hp | hp
  · have hd : f'.range ≤ Matrix.PSL3.LinearThree.pointLocalSL F.Carrier := by
      rw [←Matrix.PSL3.LinearThree.pointParabolicSL_residual F.Carrier hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let D := Matrix.PSL3.LinearThree.pointLocalSL F.Carrier
    let q := (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F.Carrier).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 D))
    have hq : Function.Surjective q :=
      (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F.Carrier).surjective.comp
        (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 D := by ext x; simp [q]
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := D)
      infer_instance
    exact hn (degree_of_local_projection hc F P' f' hl' D hd
      (hP' ▸ inf_le_left) q hq)
  · have hd : f'.range ≤ Matrix.PSL3.LinearThree.lineLocalSL F.Carrier := by
      rw [←Matrix.PSL3.LinearThree.lineParabolicSL_residual F.Carrier hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let D := Matrix.PSL3.LinearThree.lineLocalSL F.Carrier
    let q := (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F.Carrier).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 D))
    have hq : Function.Surjective q :=
      (Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F.Carrier).surjective.comp
        (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 D := by ext x; simp [q]
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := D)
      infer_instance
    exact hn (degree_of_local_projection hc F P' f' hl' D hd
      (hP' ▸ inf_le_right) q hq)

variable {G : Type*} [Group G] [Finite G]

/-- A full-Sylow local A₅ bounds the degree of a binary linear-three
containing-component quotient. Every parabolic placement and projection
hypothesis is proved from the displayed local component data. -/
public theorem source_local_component_linearThree_degree_le_two
    {H K S W L₁ : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL₁ : L₁ ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L₁)
    (F : BinaryField)
    (e : (L₁ ⧸ pCore 2 L₁) ≃* SL(3,F.Carrier)) : F.degree ≤ 2 := by
  have hlocal : K ∈ ChapterA.Section03.localCComponents S :=
    hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hSH)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hSyl hL₁.1 hL₁.2.subnormal
  have hP' : (P : Subgroup L₁) = S.subgroupOf L₁ := by
    apply map_injective L₁.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  let B := K.subgroupOf L₁
  have hlB : B ∈ ChapterA.Section03.localCComponents P := by
    rw [hP']
    exact ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hKL
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (P : Subgroup L₁))) := hlB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup L₁) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup L₁) from le_sup_left)).surjective
  let b := subgroupOfEquivOfLe hKL
  have hcB : Nat.card (B ⧸ pCore 2 B) = 60 := by
    let be := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans heK.some
    rw [Nat.card_congr be.toEquiv,nat_card_alternatingGroup]
    norm_num
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L₁))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 L₁ := by ext x; simp [q]
  let : Group.IsSolvable q.ker := by
    rw [hqker]
    let := pCore_isNilpotent (p := 2) (G := L₁)
    infer_instance
  let P' := P.mapSurjective (f := q) hq
  have hPmap : (P' : Subgroup SL(3,F.Carrier)) = (P : Subgroup L₁).map q := rfl
  let f := q.comp B.subtype
  have hl : f.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hPmap]
    simpa only [f,MonoidHom.range_comp,range_subtype] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hlB q
  have hp : f.range ⊔ (P' : Subgroup SL(3,F.Carrier)) ≠ ⊤ := by
    intro ht
    dsimp only [f] at ht
    rw [MonoidHom.range_comp,range_subtype,hPmap] at ht
    have hmap : (B ⊔ (P : Subgroup L₁)).map q = ⊤ := by
      simpa only [Subgroup.map_sup] using ht
    have hcore : pCore 2 L₁ ≤ B ⊔ (P : Subgroup L₁) :=
      (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right
    have hj : B ⊔ (P : Subgroup L₁) = ⊤ := by
      have hh := congrArg (comap q) hmap
      simpa only [comap_map_eq,hqker,sup_eq_left.mpr hcore,comap_top] using hh
    have hBC : B.IsCComponent := by
      have hb := hlB
      change (B.subgroupOf (B ⊔ (P : Subgroup L₁))).IsCComponent at hb
      rw [hj] at hb
      have hh := hb.map_subtype (show (⊤ : Subgroup L₁).IsSubnormal from .top)
      simpa only [map_subgroupOf_eq_of_le le_top] using hh
    have hLC : (⊤ : Subgroup L₁).IsCComponent := by
      have hh := hL₁.2.subgroupOf le_rfl
      rw [subgroupOf_self] at hh
      have ht := hh.map_equiv (subgroupOfEquivOfLe hL₁.1)
      simpa only [map_top_of_surjective (subgroupOfEquivOfLe hL₁.1).toMonoidHom
        (subgroupOfEquivOfLe hL₁.1).surjective] using ht
    have hb : B = ⊤ := hBC.eq_of_le hLC le_top
    have heq : K = L₁ := le_antisymm hKL (subgroupOf_eq_top.mp hb)
    subst L₁
    have hc : Nat.card SL(3,F.Carrier) = 60 := by
      rw [←Nat.card_congr e.toEquiv,Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]
      norm_num
    have hd : 2 ^ (F.degree * 3) ∣ 60 := by
      have hh := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
      rw [Matrix.PSL3.LinearThree.card_unipotentSL,F.card_eq,←pow_mul,hc] at hh
      exact hh
    have h3 : 3 ≤ F.degree * 3 := by have := F.degree_pos; omega
    have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 h3).trans hd
    norm_num at hh
  exact degree_of_proper_linearThree_join hcB F P' f hl hp

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- Both linear rows of the printed final comparison are impossible for
the original failed-parabolic wreath configuration. -/
public theorem source_HStar_wreath_five_failed_quotient_linear_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let R := (Y ⊔ S).pCoreIn 2
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁ ∧
          ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) ∧ Y ≤ L₁ ∧
          IsQuasisimple (L₁ ⧸ pCore 2 L₁) ∧
          ∀ F : ChapterB.QuasisimpleSource.BinaryField,
            4 ∣ F.degree →
              (¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* SL(2,F.Carrier))) ∧
              (¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* SL(3,F.Carrier)))) := by
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_no_large_rankOne
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq,hno⟩ :=
    hconf hcore hfailed
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq,?_⟩
  intro F hd
  refine ⟨hno F hd,?_⟩
  intro he
  have hle := source_local_component_linearThree_degree_le_two hK
    (inf_le_left.trans hH.1.1.2) heK hSyl hL₁ hKL F he.some
  have hge := Nat.le_of_dvd F.degree_pos hd
  omega

end CFSG.Quasithin.Chapter15.Section02
