module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOvercomponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.PerfectCenterFrattini
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import Theory.SpecificGroups.Suzuki.SubgroupParameters

/-!
# Ree overcomponent exclusion in the generic rank-one pair

Write K = O²(H) and R = O₂(J) for a proper local overcomponent J of K.
The actual Ree comparison puts the original S inside K, giving
O₂(H) = O₂(K) and R ≤ O₂(K). Restricting the original full Sylow to J
and mapping through J → J/R retains a proper local-component image of K.

In a Ree containing carrier, proper local components are the two genuine
parabolic residuals. The Suzuki quotient rules out the linear residual;
its order determines the odd field degree in the other residual. Thus a
solvable-kernel surjection from K onto that image has equal source and
target orders and is injective. Since R ≤ K, this forces R = 1, contrary
to characteristic two and nonsolvability of J. The same argument passes
through the center of J/R: perfectness preserves properness, and the
composite kernel remains solvable. No central-cover splitting is needed.

The Chapter12 companion applies both exclusions to the original pair,
retaining both compatible orientations, the whole overlap and every
positive Ree parameter. The full
containing-carrier selection now excludes every proper overcomponent,
proving right maximality and the literal normalizer conditions of5.3.
Exhaustive F.1.12 comparison, original uniqueness and ambient completion
recognition remain necessary for GlobalExit.

Source: Aschbacher–Smith 5.2.8, printed p.652, using A.3.12(3), pp.47–48
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.ReeEmbedding
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open BenderSuzuki.MatrixGroups

private theorem suzuki_parameter_eq {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (e : SuzukiMatrixGroup m ≃* SuzukiMatrixGroup k) : m = k := by
  have hc := Nat.card_congr e.toEquiv
  have hd := Nat.dvd_antisymm
    (suzukiMatrixGroup_degree_dvd_of_card_dvd hm hk (hc ▸ dvd_rfl))
    (suzukiMatrixGroup_degree_dvd_of_card_dvd hk hm (hc.symm ▸ dvd_rfl))
  omega

/-- A solvable-kernel epimorphism from an actual Ree Suzuki residual onto
an actual proper local component of any Ree carrier is injective. -/
theorem injective_of_local_surjection
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a : X ≃* localFactor m .suzuki)
    (htop : (⊤ : Subgroup (Model k)).IsCComponent)
    (S : Sylow 2 (Model k)) (B : Subgroup (Model k))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (f : X →* B) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    Function.Injective f := by
  let aq := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (suzukiLocalQuotientEquiv m)
  let : IsSimpleGroup (SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup (X ⧸ pCore 2 X) := aq.isSimpleGroup
  let fq := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f hf
  obtain ⟨g,s,hs⟩ := ReeLocal.local_placement (by omega) htop S B hB hproper
  let b : B ≃* localFactor k s := ((MulAut.conj g).subgroupMap B).trans
    (MulEquiv.subgroupCongr hs)
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  cases s with
  | linear =>
    let c := linearLocalQuotientEquiv k
    have hlin : ClassicalGroup.IsPSL (localFactor k .linear ⧸ pCore 2 (localFactor k .linear))
        2 (2^(2*k+1)) :=
      ⟨CoefficientField k,inferInstance,inferInstance,field_card k,⟨c⟩⟩
    exact (binary_quotient_not_suzuki hlin hm ⟨bq.symm.trans (fq.symm.trans aq)⟩).elim
  | suzuki =>
    have he : m = k := suzuki_parameter_eq hm hk
      (aq.symm.trans (fq.trans (bq.trans (suzukiLocalQuotientEquiv k))))
    have hc : Nat.card X = Nat.card B := by
      rw [Nat.card_congr a.toEquiv,Nat.card_congr b.toEquiv,he]
    exact ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩).1

private theorem injective_of_local_range
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [Group.IsPerfect X]
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (b : X ≃* localFactor m .suzuki) (a : Y ≃* Model k)
    (htop : (⊤ : Subgroup Y).IsCComponent) (S : Sylow 2 Y)
    (f₀ : X →* Y) (hlocal : f₀.range ∈ localCComponents S)
    (hproper : f₀.range ≠ ⊤) [Group.IsSolvable f₀.ker] : Function.Injective f₀ := by
  let f := a.toMonoidHom.comp f₀
  let S' : Sylow 2 (Model k) := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,MonoidHom.ker_comp_of_injective f₀ a.toMonoidHom a.injective]
    infer_instance
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have ht : (⊤ : Subgroup (Model k)).IsCComponent := by
    simpa only [map_top_of_surjective a.toMonoidHom a.surjective] using htop.map_equiv a
  have hC : f.range ∈ localCComponents S' := by
    change (a.toMonoidHom.comp f₀).range ∈
      localCComponents ((S : Subgroup Y).map a.toMonoidHom)
    rw [MonoidHom.range_comp]
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal a.toMonoidHom
  have hCproper : f.range ≠ ⊤ := by
    intro hc
    apply hproper
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_top_of_surjective a.toMonoidHom a.surjective]
    simpa only [f,MonoidHom.range_comp] using hc
  have hinj := injective_of_local_surjection hm hk b ht S' f.range hC hCproper
    f.rangeRestrict f.rangeRestrict_surjective
  exact fun x y hxy => hinj (Subtype.ext (congrArg a hxy))

private theorem injective_of_central_local_range
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y] [Group.IsPerfect X]
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (b : X ≃* localFactor m .suzuki) (a : (Y ⧸ center Y) ≃* Model k)
    (htop : (⊤ : Subgroup Y).IsCComponent) (S : Sylow 2 Y)
    (f₀ : X →* Y) (hlocal : f₀.range ∈ localCComponents S)
    (hproper : f₀.range ≠ ⊤) [Group.IsSolvable f₀.ker] : Function.Injective f₀ := by
  let : Group.IsPerfect (⊤ : Subgroup Y) := htop.perfect
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := Y)).toMonoidHom) (topEquiv (G := Y)).surjective
  let q := QuotientGroup.mk' (center Y)
  let f := q.comp f₀
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm (fun x y => IsMulCommutative.is_comm.comm x y)
  let : Group.IsSolvable f.ker := by
    rw [←MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker f₀ q.ker
  have ht : (⊤ : Subgroup (Y ⧸ center Y)).IsCComponent := by
    simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using
      cComponent_map_of_solvable_ker htop q (QuotientGroup.mk'_surjective _)
  let S' : Sylow 2 (Y ⧸ center Y) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hl : f.range ∈ localCComponents S' := by
    simpa only [f,S',Sylow.coe_mapSurjective,MonoidHom.range_comp] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal q
  have hn : f.range ≠ ⊤ := by
    intro he
    apply hproper
    apply eq_top_of_sup_center_eq_top f₀.range
    have hh := congrArg (Subgroup.comap q) he
    simpa only [f,MonoidHom.range_comp,comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  have hi := injective_of_local_range hm hk b a ht S' f hl hn
  exact fun x y hxy => hi (congrArg q hxy)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.ReeEmbedding

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]

private theorem ree_residual_mem_local
    {T : Sylow 2 G} {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (a : (residual H ⧸ pCore 2 (residual H)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    residual H ∈ Chapter1.L G (T : Subgroup G) := by
  rcases hH with ⟨hH,hTH⟩
  change (T : Subgroup G) ≤ H at hTH
  let := hp
  let : IsSimpleGroup (residual H ⧸ pCore 2 (residual H)) :=
    a.isSimpleGroup_congr.mpr
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  have hz : center (residual H ⧸ pCore 2 (residual H)) = ⊥ :=
    (inferInstance : (center (residual H ⧸ pCore 2 (residual H))).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht))
  let : IsQuasisimple (residual H ⧸ pCore 2 (residual H)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hRH : residual H ≤ H := map_subtype_le _
  let e := (subgroupOfEquivOfLe hRH).symm
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (((residual H).subgroupOf H) ⧸ pCore 2 ((residual H).subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q
  have hn : ((residual H).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_residual H)
  have hc := isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((isPPerfect_embedded_pResidual 2 H).of_surjective e.toMonoidHom e.surjective)
  change ((residual H).subgroupOf (residual H ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [residual_sup_sylow T H hTH]
  refine ⟨hc,⟨T.subtype hTH,?_⟩,hH⟩
  simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]

private theorem ree_embedding_context
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hRK : J.pCoreIn 2 ≤ normalizer (K : Set G))
    (hpK : Group.IsPerfect K) :
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ.le)
    IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) ∧
      (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent ∧ f.range ≠ ⊤ ∧
      ∃ S : Sylow 2 J, (S : Subgroup J) = (T : Subgroup G).subgroupOf J ∧
        (let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
         f.range ∈ ChapterA.Section03.localCComponents Sb ∧
           (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (f.range : Set _)) := by
  let X := J ⊔ (T : Subgroup G)
  let JX := J.subgroupOf X
  let eJ : JX ≃* J := subgroupOfEquivOfLe le_sup_left
  let TX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨P,hP⟩ := TX.exists_subgroupOf_eq_of_subnormal JX hJ.1.subnormal
  let S := P.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hSJ : (S : Subgroup J) = (T : Subgroup G).subgroupOf J := by
    change (P : Subgroup JX).map eJ.toMonoidHom = _
    rw [hP]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hy
      exact ⟨eJ.symm y,hy,eJ.apply_symm_apply y⟩
  have hSK : (S : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ.le]
    rw [hSJ]
    exact comap_mono hTK
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion hKJ.le)
  let B := f.range
  have hBmap : B = (K.subgroupOf J).map q := by
    change (q.comp (inclusion hKJ.le)).range = _
    rw [MonoidHom.range_comp,inclusion_range]
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hnorm : (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (B : Set _) := by
    rw [hBmap]
    exact (map_mono hSK).trans (le_normalizer_map q)
  have hb : B ∈ ChapterA.Section03.localCComponents Sb := by
    have hl := ChapterA.Section03.SourceEmbeddings.local_restrict hK.1 hKJ.le
    rw [←hSJ] at hl
    let : Group.IsSolvable q.ker := by
      rw [QuotientGroup.ker_mk']
      let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
      infer_instance
    change B ∈ ChapterA.Section03.localCComponents ((S : Subgroup J).map q)
    simpa only [hBmap] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hne : B ≠ ⊤ := by
    intro ht
    let D := K.subgroupOf J
    have hgen : D ⊔ pCore 2 J = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      rw [hBmap,comap_map_eq,QuotientGroup.ker_mk',comap_top] at hh
      exact hh
    have hnD : D.Normal := (normalizer_eq_top_iff).mp (by
      have hh : D ⊔ pCore 2 J ≤ normalizer (D : Set J) := by
        refine sup_le D.le_normalizer ?_
        rw [←subgroupOf_normalizer_eq hKJ.le]
        intro x hx
        exact hRK (mem_map_of_mem J.subtype hx)
      rw [hgen] at hh
      exact top_unique hh)
    let := hnD
    let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hKJ.le).symm.toMonoidHom)
      (subgroupOfEquivOfLe hKJ.le).symm.surjective
    let : Group.IsPerfect J := Chapter1.mem_L_isPerfect hJ
    have hDtop : D = ⊤ :=
      (residuals_of_perfect_normal_sup_twoGroup D (pCore 2 J) pCore_isPGroup hgen).2.symm.trans
        solvableResidual_eq_top
    exact hKJ.ne (le_antisymm hKJ.le (subgroupOf_eq_top.mp hDtop))
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hsq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hJ.2.2
  let eqJ : JX.map qX ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans
      (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) :=
    (IsSQTK.equiv eqJ).mp (hsq.subgroup _)
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := X)
    have hh : (⊤ : Subgroup (JX.map qX)).IsCComponent := by
      simpa only [subgroupOf_self] using (hJ.1.map_quotient (pCore 2 X)).subgroupOf le_rfl
    simpa only [map_top_of_surjective eqJ.toMonoidHom eqJ.surjective] using hh.map_equiv eqJ
  exact ⟨hsqJ,htop,hne,S,hSJ,hb,hnorm⟩

/-- In the Ree row the original S is contained in the right residual, so
every containing local component has its two-core inside that same residual. -/
theorem Preparation.ree_overcomponent_core_le
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    H.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      J.pCoreIn 2 ≤ (residual H).pCoreIn 2 := by
  have hm := d.ree_parameter_positive h hp m 1 .suzuki e.right
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := parabolic m .suzuki
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hr := parabolic_solvableResidual_map hm .suzuki
  let U := ((sourceS L H).subgroupOf P).map e.right.toMonoidHom
  have hU : IsPGroup 2 U :=
    (((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map e.right.toMonoidHom)
  let S := (ReeFour.sylow m).subtype
    ((ReeFour.sylow_le_localFactor m .suzuki).trans (localFactor_le_parabolic m .suzuki))
  have hS : (S : Subgroup Q) ≤ solvableResidual Q := by
    intro x hx
    have hxK := ReeFour.sylow_le_localFactor m .suzuki hx
    rw [←hr] at hxK
    obtain ⟨y,hy,he⟩ := hxK
    exact (Subtype.ext he : y = x) ▸ hy
  have hn : ¬ 2 ∣ (solvableResidual Q).index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le hS))
  have hle : U ≤ solvableResidual Q :=
    IsPGroup.le_normal_of_index_primeTo _ U hU hn
  change ((sourceS L H).subgroupOf P).map e.right.toMonoidHom ≤ _ at hle
  rw [←map_solvableResidual_eq e.right.toMonoidHom e.right.surjective,
    map_le_map_iff_of_injective e.right.injective] at hle
  have hs := map_mono (f := P.subtype) hle
  rw [map_subgroupOf_eq_of_le hSP,d.parabolic_residuals h hTH hp 1] at hs
  have hc := residual_core_eq_of_sourceS_le h.sylow_normalizes hTH hs
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [←residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ le_rfl
  exact ⟨hc,(pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
    le_sup_left hJ.1.subnormal).trans
      ((Chapter3.twoCore_le_of_sylow_le T hTH hHJ).trans_eq hc)⟩

private theorem quotient_inclusion_not_injective
    {T : Sylow 2 G} {K J : Subgroup G} (hE : IsEvenCharacteristicAt T)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (hRK : J.pCoreIn 2 ≤ K) :
    ¬ Function.Injective ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)) := by
  intro hi
  let f₀ := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
  have hc : pCore 2 J = ⊥ := by
    apply bot_unique
    intro x hx
    let y : K := ⟨x,hRK (mem_map_of_mem J.subtype hx)⟩
    have hy : f₀ y = f₀ 1 := by
      rw [map_one]
      exact (QuotientGroup.eq_one_iff _).mpr hx
    exact mem_bot.mpr (Subtype.ext (congrArg (fun z : K => (z : G)) (hi hy)))
  have hchar := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T hE hJ
  have hzero : (⊤ : Subgroup J) ≤ ⊥ := by
    intro x _
    rw [←hc]
    apply hchar
    intro y hy
    have hy1 : y = 1 := mem_bot.mp (hc ▸ hy)
    simp only [hy1,one_mul,mul_one]
  have hJzero : J = ⊥ := by
    apply bot_unique
    intro x hx
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp (hzero (mem_top (⟨x,hx⟩ : J)))))
  apply Chapter1.mem_L_not_isSolvable hJ
  rw [hJzero]
  infer_instance

/-- The original Ree right residual has no proper local overcomponent whose
literal two-core quotient is a Ree carrier, at any positive field parameter. -/
theorem Preparation.not_ree_overcomponent
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H < J)
    {k : ℕ} (hk : 0 < k) : ¬ Nonempty ((J ⧸ pCore 2 J) ≃* Model k) := by
  intro ⟨a⟩
  have hTH := hH.1.1.2
  rcases he with he | he
  · exact d.not_ree_unreversed h hTH hp m he
  obtain ⟨e⟩ := he
  obtain ⟨_,hm,_,⟨b⟩,⟨bq⟩,_⟩ := d.ree_local_structure h hTH hp m e
  have hK := ree_residual_mem_local hH.1.1 hp m hm bq
  have hR := (d.ree_overcomponent_core_le h hTH hp m e hJ hKJ.le).2
  have hRK : J.pCoreIn 2 ≤ residual H := hR.trans (map_subtype_le _)
  obtain ⟨_,htop,hproper,S,_,hlocal,_⟩ := ree_embedding_context h.qtke hK hJ
    (hTH.trans (le_normalizer_residual H)) hKJ (hRK.trans (residual H).le_normalizer) hp
  let q := QuotientGroup.mk' (pCore 2 J)
  let f₀ := q.comp (inclusion hKJ.le)
  let := hp
  let : Group.IsSolvable f₀.ker := by
    have hi : IsPGroup 2 f₀.ker := by
      rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_of_injective (inclusion hKJ.le) (inclusion_injective _)
    let := hi.isNilpotent
    infer_instance
  have hi := ReeEmbedding.injective_of_local_range hm hk b a htop
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) f₀ hlocal hproper
  exact quotient_inclusion_not_injective (h.qtke.evenCharacteristic T) hJ hKJ.le hRK hi

/-- The same contradiction excludes all central Ree covers in the literal
two-core quotient; no center-triviality or splitting assumption is needed. -/
theorem Preparation.not_ree_central_overcomponent
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H < J)
    {k : ℕ} (hk : 0 < k) : ¬ Nonempty (((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ≃* Model k) := by
  intro ⟨a⟩
  have hTH := hH.1.1.2
  rcases he with he | he
  · exact d.not_ree_unreversed h hTH hp m he
  obtain ⟨e⟩ := he
  obtain ⟨_,hm,_,⟨b⟩,⟨bq⟩,_⟩ := d.ree_local_structure h hTH hp m e
  have hK := ree_residual_mem_local hH.1.1 hp m hm bq
  have hR := (d.ree_overcomponent_core_le h hTH hp m e hJ hKJ.le).2
  have hRK : J.pCoreIn 2 ≤ residual H := hR.trans (map_subtype_le _)
  obtain ⟨_,htop,hproper,S,_,hlocal,_⟩ := ree_embedding_context h.qtke hK hJ
    (hTH.trans (le_normalizer_residual H)) hKJ (hRK.trans (residual H).le_normalizer) hp
  let q := QuotientGroup.mk' (pCore 2 J)
  let f₀ := q.comp (inclusion hKJ.le)
  let := hp
  let : Group.IsSolvable f₀.ker := by
    have hi : IsPGroup 2 f₀.ker := by
      rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_of_injective (inclusion hKJ.le) (inclusion_injective _)
    let := hi.isNilpotent
    infer_instance
  have hi := ReeEmbedding.injective_of_central_local_range hm hk b a htop
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) f₀ hlocal hproper
  exact quotient_inclusion_not_injective (h.qtke.evenCharacteristic T) hJ hKJ.le hRK hi

/-- The actual Ree right residual is maximal among the original local
components. The containing-carrier selection and both quotient steps are discharged. -/
theorem Preparation.ree_right_maximal
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hTH := hH.1.1.2
  rcases he with he | he
  · exact (d.not_ree_unreversed h hTH hp m he).elim
  obtain ⟨e⟩ := he
  obtain ⟨_,hm,_,_,⟨bq⟩,_⟩ := d.ree_local_structure h hTH hp m e
  have hK := ree_residual_mem_local hH.1.1 hp m hm bq
  let := hp
  refine ⟨hK,?_⟩
  intro J hJ hKJ
  by_contra hne
  have hlt : residual H < J := lt_of_le_of_ne hKJ (Ne.symm hne)
  have hR := (d.ree_overcomponent_core_le h hTH hp m e hJ hKJ).2
  have hRK : J.pCoreIn 2 ≤ residual H := hR.trans (map_subtype_le _)
  obtain ⟨hsq,htop,hproper,S,_,hlocal,hnorm⟩ := ree_embedding_context h.qtke hK hJ
    (hTH.trans (le_normalizer_residual H)) hlt (hRK.trans (residual H).le_normalizer) hp
  let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion hKJ)
  have hker : IsPGroup 2 f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective (inclusion hKJ) (inclusion_injective _)
  let aq := (MonoidHom.quotientPCoreEquivOfSurjective f.rangeRestrict
    f.rangeRestrict_surjective hker).symm.trans bq
  obtain ⟨k,hk,heq⟩ := ReeContaining.central_quotient_ree hsq (pCore_quotient_pCore_eq_bot 2)
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) f.range hlocal hnorm htop hproper hm aq
  exact d.not_ree_central_overcomponent h hH hp m (.inr ⟨e⟩) hJ hlt hk heq

/-- The Ree branch satisfies the literal normalizer conditions of 5.3,
with right maximality, common Sylow and enlarged two-cores discharged. -/
theorem Preparation.ree_normalizer_local_conditions
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .ree m he
  exact d.normalizer_local_conditions h hH (d.ree_right_maximal h hH hp m he) rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
