module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicLocalContainers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFourSections

/-!
# Excluding J₄ and cubic M₂₂ common containers

The retained original residual quotient is the full SL₃(4), of order 60480.
A non-solvable quotient of this cover has order 60480 or 20160: its kernel
is central and has order one or three. Applying this to the literal maps
on intrinsic two-core quotients preserves the cubic-kernel alternative.
The full-Sylow M₂₂ section theorem excludes order 20160, while the order
of M₂₂ excludes 60480. This removes the full cubic M₂₂ common cover.

For J₄, even characteristic and the faithful Sylow bound first force a
nontrivial local two-core. The native elementary-normalizer catalogue then
places the pair in the M₂₄ local subgroup or supplies an invariant elementary
group of order at most eight. The SL₃(4) section acts trivially on that small
group, placing the full pair in an involution centralizer. The first
centralizer maps with solvable kernel to M₂₂; the second has insufficient
two-part. The M₂₄ local quotient alternatives also have incompatible orders.

The source application uses the original residual's full Sylow restriction,
not a full-Sylow assumption on the selected parabolic. It retains the same
pair, relative normality, strict changed orbit, original Cartans and fields.
Rank-two, Held and binary SL₃ common containers, zero-core recognition and
the higher-field generation argument remain open.

Source: Aschbacher–Smith A.3.12 and 5.2.2, printed pp.47–48,648–649,
refs/quasithin.pdf; GLS3 Table5.3i for the actual J₄ local carriers.
The imported native certificates retain their ATLAS attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem sl3_four_quotient_card {Y Z : Type*} [Group Y] [Group Z] [Finite Z]
    (hm : IsSL Y 3 4) (f : Y →* Z) (hf : Function.Surjective f)
    (hns : ¬ Group.IsSolvable Z) : Nat.card Z = 20160 ∨ Nat.card Z = 60480 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let g := f.comp e.symm.toMonoidHom
  have hg : Function.Surjective g := hf.comp e.symm.surjective
  let : IsQuasisimple SL(3,F) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  have hker : g.ker ≤ center SL(3,F) :=
    (IsQuasisimple.normal_le_center_or_eq_top g.ker).resolve_right (by
      intro ht
      have hone : ∀ z : Z, z = 1 := by
        intro z
        obtain ⟨x,rfl⟩ := hg z
        exact MonoidHom.mem_ker.mp (ht ▸ mem_top x)
      exact hns (Group.isSolvable_of_comm (fun x y => by rw [hone x,hone y])))
  have hc : Nat.card g.ker ∣ 3 := by
    have hh := card_dvd_of_le hker
    rw [Atlas.ExceptionalSupport.card_sl_center,hF] at hh
    exact hh
  have hprod := g.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr hg, Nat.card_congr (topEquiv (G := Z)).toEquiv,
    Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hprod
  rcases (Nat.dvd_prime Nat.prime_three).mp hc with hc | hc
  · right; rw [hc] at hprod; norm_num at hprod; exact hprod
  · left; rw [hc] at hprod; norm_num at hprod; omega

private theorem local_core_nonsolvable {Y : Type*} [Group Y] [Finite Y]
    {S B : Subgroup Y} (hl : B ∈ ChapterA.Section03.localCComponents S) :
    ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
  intro hsol
  let := hsol
  let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
  let : Group.IsSolvable B := Group.isSolvable_of_ker_le_range
    (pCore 2 B).subtype (QuotientGroup.mk' (pCore 2 B)) (by
      rw [range_subtype,QuotientGroup.ker_mk'])
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact hl.not_isSolvable (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

private theorem sl3_four_image_core_card {Y Z : Type*} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (f : Y →* Z) (hf : Function.Surjective f)
    (hm : IsSL (Y ⧸ pCore 2 Y) 3 4)
    (hns : ¬ Group.IsSolvable (Z ⧸ pCore 2 Z)) :
    Nat.card (Z ⧸ pCore 2 Z) = 20160 ∨ Nat.card (Z ⧸ pCore 2 Z) = 60480 := by
  have hmap : (pCore 2 Y).map f ≤ pCore 2 Z :=
    le_sSup ⟨(inferInstance : (pCore 2 Y).Normal).map f hf,pCore_isPGroup.map f⟩
  let q := QuotientGroup.map (pCore 2 Y) (pCore 2 Z) f (map_le_iff_le_comap.mp hmap)
  have hq : Function.Surjective q := QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hf) _
  exact sl3_four_quotient_card hm q hq hns

private theorem sl3_four_not_mathieu_surjection
    {Y Z : Type*} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (q : Y →* Z) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) (e : Z ≃* Sporadic.Mathieu.M22) : False := by
  let P := S.mapSurjective hq
  have hlq := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have hnq := (map_mono hn).trans (B.le_normalizer_map q)
  rcases sl3_four_image_core_card (q.subgroupMap B) (q.subgroupMap_surjective B) hm
      (local_core_nonsolvable hlq) with hc | hc
  · exact Exceptional.not_mathieu_twentyTwo_of_section_card P (B.map q) hnq hc e
  · have hd := (card_quotient_dvd_card (pCore 2 (B.map q))).trans (B.map q).card_subgroup_dvd_card
    rw [hc,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order] at hd
    norm_num at hd


private theorem sl3_four_card {Y : Type*} [Group Y] (hm : IsSL Y 3 4) : Nat.card Y = 60480 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
  norm_num

private theorem sl3_four_quasisimple {Y : Type*} [Group Y] (hm : IsSL Y 3 4) : IsQuasisimple Y := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
  exact IsQuasisimple.of_mulEquiv e.symm

private theorem sl3_of_equiv {Y Z : Type*} [Group Y] [Group Z]
    (hm : IsSL Z 3 4) (e : Y ≃* Z) : IsSL Y 3 4 := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
  exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩

private theorem small_action {Y E : Type*} [Group Y] [Finite Y] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hm : IsSL (B ⧸ pCore 2 B) 3 4)
    (hE : Nat.card E ≤ 8) (f : B →* MulAut E) : f = 1 := by
  by_contra hf
  let B' := B.subgroupOf (B ⊔ (S : Subgroup Y))
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup Y) from le_sup_left)
  let g := f.comp e.toMonoidHom
  have hk : g.ker ≠ ⊤ := by
    intro ht
    apply hf
    apply MonoidHom.ext
    intro x
    change f x = 1
    have hx : e.symm x ∈ g.ker := ht ▸ mem_top _
    simpa [g] using hx
  let : Group.IsSolvable g.ker :=
    hl.isSolvable_of_subnormal_lt_top (inferInstance : g.ker.Normal).isSubnormal hk
  let : Group.IsSolvable g.rangeRestrict.ker := by rw [MonoidHom.ker_rangeRestrict]; infer_instance
  have hns : ¬ Group.IsSolvable (g.range ⧸ pCore 2 g.range) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 g.range) := pCore_isNilpotent
    let : Group.IsSolvable g.range := Group.isSolvable_of_ker_le_range
      (pCore 2 g.range).subtype (QuotientGroup.mk' (pCore 2 g.range)) (by
        rw [range_subtype,QuotientGroup.ker_mk'])
    exact hl.not_isSolvable (Group.isSolvable_of_ker_le_range
      g.rangeRestrict.ker.subtype g.rangeRestrict (by rw [range_subtype]))
  have h168 : Nat.card (MulAut E) ∣ 168 := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa [←hk] using hE)
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E k hk]
    interval_cases k <;> norm_num [Fin.prod_univ_succ]
  have hd := (card_quotient_dvd_card (pCore 2 g.range)).trans
    (g.range.card_subgroup_dvd_card.trans h168)
  have hm' := sl3_of_equiv hm (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  rcases sl3_four_image_core_card g.rangeRestrict g.rangeRestrict_surjective hm' hns with hc | hc
  all_goals rw [hc] at hd; norm_num at hd

open FiveLocalFF.SolvableQuotients
open Janko4 Janko4.Cardinality Janko4.LocalStructure
open Janko4.OuterReduction.OddIndex
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four

private theorem max1_not (hQ : IsSQTK KnownSimple.IsKnownSimple M)
    (S : Sylow 2 M) (B : Subgroup M)
    (hl : B ∈ ChapterA.Section03.localCComponents S) (hn : (S : Subgroup M) ≤ normalizer (B : Set M))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) : False := by
  have hc := sl3_four_card hm
  have h7 : 7 ∣ Nat.card (B ⧸ pCore 2 B) := by rw [hc]; norm_num
  rcases JankoMathieu.max1_local_models hQ S B hl hn (sl3_four_quasisimple hm) h7 with
    hb | ⟨F,_,_,hF,⟨a⟩⟩ | ha
  · omega
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF,←Nat.card_congr a.toEquiv,hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · obtain ⟨a⟩ := ha
    rw [Nat.card_congr a.toEquiv,Sporadic.Mathieu.m24_order] at hc
    norm_num at hc
private theorem first_not (S : Sylow 2 InvolutionCentralizers.First.centralizer)
    (B : Subgroup InvolutionCentralizers.First.centralizer)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup InvolutionCentralizers.First.centralizer) ≤
      normalizer (B : Set InvolutionCentralizers.First.centralizer))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) :
    False := by
  open InvolutionCentralizers.First InvolutionCentralizers.First.QuotientExtension in
  let := local_perfect hl
  let : Group.IsSolvable (centralizer ⧸ H) :=
    Group.isSolvable_of_surjective (f := centralizerQuotientEquivC2.symm.toMonoidHom)
      centralizerQuotientEquivC2.symm.surjective
  have hBH : B ≤ H := le_of_isPerfect_of_solvable_quotient B H
  obtain ⟨P,hP,hBP⟩ := exists_local_sylow_restriction S hl hBH
    (inferInstance : H.Normal).isSubnormal
  let d := subgroupOfEquivOfLe hBH
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hn' : (P : Subgroup H) ≤ normalizer (B.subgroupOf H : Set H) := by
    rw [hP,←subgroupOf_normalizer_eq hBH]
    exact comap_mono hn
  let : Group.IsNilpotent (Q.subgroupOf R) :=
    (show IsPGroup 2 (Q.subgroupOf R) from pCore_isPGroup.comap_subtype).isNilpotent
  let : Group.IsSolvable scalarSubgroup := Group.isSolvable_of_surjective
    (f := scalarSubgroupEquivC3.symm.toMonoidHom) scalarSubgroupEquivC3.symm.surjective
  let : Group.IsSolvable R := Group.isSolvable_of_ker_le_range
    (Q.subgroupOf R).subtype scalarProjection (by rw [range_subtype,scalarProjection_ker])
  let : Group.IsSolvable mathieuProjection.ker := by
    rw [mathieuProjection_ker]
    exact Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe R_le_H).symm.toMonoidHom)
      (subgroupOfEquivOfLe R_le_H).symm.surjective
  exact sl3_four_not_mathieu_surjection mathieuProjection mathieuProjection_surjective P
    (B.subgroupOf H) hBP hn' (sl3_of_equiv hm e) (MulEquiv.refl _)

private theorem core_ne_bot (hQ : IsSQTK KnownSimple.IsKnownSimple Model)
    (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) : pCore 2 B ≠ ⊥ := by
  intro hc
  let a : B ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc).symm
  let : IsQuasisimple B := sl3_four_quasisimple (sl3_of_equiv hm a)
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S
    (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic S) hl hn
  have hcard : Nat.card B = 60480 := (Nat.card_congr a.toEquiv).trans (sl3_four_card hm)
  have he := JankoRank.eq_top_of_quasisimple_faithful_sylow (MulEquiv.refl _) S B
    (hQ.subgroup B) hc (by rw [hcard]; norm_num) hn hf
  rw [he,Nat.card_congr (topEquiv (G := Model)).toEquiv,Cardinality.model_card] at hcard
  norm_num at hcard

private noncomputable def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_not (hQ : IsSQTK KnownSimple.IsKnownSimple Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents markedSylow)
    (hn : twoSubgroup ≤ normalizer (B : Set Model))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) :
    False := by
  obtain ⟨N,hN,hBN,hSN⟩ := exists_maximal_two_local markedSylow B hn
    (core_ne_bot hQ markedSylow B hl hn hm)
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  let E := R.map (markedSylow : Subgroup Model).subtype
  have he : IsElementaryAbelian 2 E := by let := heR; exact IsElementaryAbelian.map _
  have hne : E ≠ ⊥ := fun hz => hR ((map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hz)
  have hBE : B ≤ normalizer (E : Set Model) := hNR ▸ hBN
  have hSE : twoSubgroup ≤ normalizer (E : Set Model) := hNR ▸ hSN
  rcases FiveLocalFF.JankoFour.fixed_pair_minimal_alternative (B ⊔ twoSubgroup) E
    (map_subtype_le R) hne he le_sup_right (sup_le hBE hSE) with hmax | ⟨A,hA,hAE,heA,hcard,hBA⟩
  · have hBM := le_sup_left.trans hmax
    let d := subgroupOfEquivOfLe hBM
    let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    exact max1_not (hQ.subgroup M) (markedSylow.subtype (le_sup_right.trans hmax)) (B.subgroupOf M)
      (local_restrict hl hBM) (by rw [←subgroupOf_normalizer_eq hBM]; exact comap_mono hn)
      (sl3_of_equiv hm e)
  · let := heA
    let f := A.normalizerMonoidHom.comp (inclusion (le_sup_left.trans hBA))
    have hf := small_action markedSylow B hl hm hcard f
    have hBC : B ≤ centralizer (A : Set Model) := by
      intro b hb
      have hh : inclusion (le_sup_left.trans hBA) ⟨b,hb⟩ ∈ A.normalizerMonoidHom.ker := by
        change f ⟨b,hb⟩ = 1
        rw [hf]
        rfl
      rwa [normalizerMonoidHom_ker] at hh
    have h2 : 2 ∣ Nat.card (centralizer (B : Set Model)) := by
      obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have hk0 : k ≠ 0 := by
        intro hz
        rw [hz,pow_zero] at hk
        exact hA (A.eq_bot_of_card_eq hk)
      exact (by rw [hk]; exact dvd_pow_self 2 hk0 : 2 ∣ Nat.card A).trans
        (card_dvd_of_le (le_centralizer_iff.mp hBC))
    obtain ⟨z,hz,hpair⟩ := exists_involution_centralizing_normalizing_two_group B twoSubgroup
      markedSylow.isPGroup' hn h2
    let C := centralizer ({z} : Set Model)
    have hBC : B ≤ C := le_sup_left.trans hpair
    have hSC : twoSubgroup ≤ C := le_sup_right.trans hpair
    rcases InvolutionCentralizers.centralizer_equiv_first_or_second z hz with he | he
    · let e := he.some
      let d := subgroupOfEquivOfLe hBC
      let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
      let b := e.subgroupMap (B.subgroupOf C)
      let c := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
      let : Group.IsSolvable e.toMonoidHom.ker := by
        rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
      have hnC : ((markedSylow.subtype hSC) : Subgroup C) ≤ normalizer (B.subgroupOf C : Set C) := by
        rw [←subgroupOf_normalizer_eq hBC]; exact comap_mono hn
      exact first_not ((markedSylow.subtype hSC).mapSurjective e.surjective)
        ((B.subgroupOf C).map e.toMonoidHom)
        (Chapter1.Section02.localCComponents_map_of_solvable_ker (local_restrict hl hBC) e.toMonoidHom)
        ((map_mono hnC).trans (le_normalizer_map e.toMonoidHom))
        (sl3_of_equiv hm (c.symm.trans a))
    · have hd := (show 2^21 ∣ Nat.card markedSylow by rw [ambient_sylow_card]).trans
        (card_dvd_of_le hSC)
      rw [Nat.card_congr he.some.toEquiv,InvolutionCentralizers.Second.ambient_card] at hd
      norm_num at hd

/-- A local SL₃(4) core quotient cannot be normalized by a full Sylow of J₄. -/
theorem jankoFour_not_sl3_four {Y : Type*} [Group Y] [Finite Y]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Y) (e : Y ≃* Model) (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) :
    False := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model Q markedSylow
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup Y).map f.toMonoidHom = twoSubgroup := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S : Subgroup Y).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    exact (map_map _ _ _).symm.trans hh
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]; infer_instance
  let d := f.subgroupMap B
  let a := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hn).trans (le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  exact fixed_not (hQ.knownSimple_of_equiv e) (B.map f.toMonoidHom) hl' hn' (sl3_of_equiv hm a.symm)


/-- The full cubic M₂₂ cover cannot contain the retained SL₃(4) local quotient. -/
theorem m22Cover_not_sl3_four {Y : Type*} [Group Y] [Finite Y]
    (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    (hm : IsSL (B ⧸ pCore 2 B) 3 4) (hcover : IsM22Cover Y) : False := by
  let q := QuotientGroup.mk' (center Y)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm (fun x y => Subtype.ext (mem_center_iff.mp y.property x))
  exact sl3_four_not_mathieu_surjection q (QuotientGroup.mk'_surjective _) S B hl hn hm hcover.2.2.some

variable {G : Type*} [Group G] [Finite G]

/-- The original full-Sylow SL₃(4) residual excludes J₄ and the full cubic M₂₂ cover. -/
theorem SelectedSourceModels.parabolic_common_not_janko_or_cubic
    {T : Sylow 2 G} {L W H R X I : Subgroup G} {n : ℕ}
    (hs : SelectedSourceModels H R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hX : X ∈ Chapter1.H G) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hm : IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    ¬ (Nonempty (Ibar ≃* Janko4.Model) ∨ IsM22Cover Ibar) := by
  let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  obtain ⟨S,V,hl,hN,hSL⟩ := original_residual_sl3_local_image hs hn hH.1.1.2 hHX hIX hI hKI hm
  dsimp only
  intro hm
  rcases hm with he | hcover
  · have hQ := Chapter3.sqtk_of_mem_H h.qtke hX
    have hbar := ChapterE.Structure.sqtk_two_quotient hQ (pCore 2 X) pCore_isPGroup
    exact jankoFour_not_sl3_four (hbar.subgroup Ibar) he.some S V hl hN hSL
  · exact m22Cover_not_sl3_four S V hl hN hSL hcover

/-- On the same selected pair, only rank-two, Held and binary SL₃ common containers remain. -/
theorem source_prime_pair_parabolic_janko_mathieu_exclusion
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  (RankTwoTheoremC Ibar ∨ Nonempty (Ibar ≃* Held.He))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    (∃ f : ℕ, 1 ≤ f ∧ (2^f) % 3 = 1 ∧ IsSL Ibar 3 (2^f)))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_local_containers h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,?_⟩
  have hnot := hs.parabolic_common_not_janko_or_cubic h hH hn
    (d.common_normal_overgroup h hH c hd hz).1 le_sup_right hIX hI hKI
  rcases hm with ⟨hsi,hm⟩ | ⟨hc,hm⟩
  · refine .inl ⟨hsi,?_⟩
    rcases hm with hrank | he | ⟨_,hSL,he⟩
    · exact .inl hrank
    · exact .inr he
    · exact (hnot hSL (.inl he)).elim
  · refine .inr ⟨hc,?_⟩
    rcases hm with hm | ⟨hm,_,hSL⟩
    · exact hm
    · exact (hnot hSL (.inr hm)).elim

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
