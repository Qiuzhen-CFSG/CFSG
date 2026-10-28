module
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuLocal
public import CFSG.Quasithin.ChapterF.Section01.RankOneOddPrime
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoFirstCentralizer
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.GoodCentralizers.Geometry
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# Rank-one local sections in the actual J₄ carrier

A local component with simple rank-one two-core quotient, normalized by a full
Sylow two-subgroup, has quotient PSL₂(4). Trivial two-core would make the Sylow
action faithful, contradicting the native rank-eleven automorphism bound.
For nontrivial core, the native elementary-normalizer catalogue gives either
the actual M₂₄ quotient or an invariant elementary group of order at most eight.
Every rank-one local component fixes that small group, so the pair lies in an
involution centralizer. The second centralizer has insufficient two-part;
the first reduces through its full 3.M₂₂.2 quotient to the checked M₂₂ theorem.
All restrictions preserve the full normalizing Sylow and the intrinsic quotient.

The original Cartan application is in the companion JankoFourNonA5 module.
This is a full-Sylow result, not the distinct relative-Sylow problem in13.3.16.
Source: Aschbacher–Smith A.3.12,5.1.12 and5.2.2, pp.47–48,635,648–649;
GLS3 Table5.3i for J₄. Imported matrix certificates retain their ATLAS provenance.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoFourSections
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open FiveLocalFF.SolvableQuotients Janko4 Janko4.Cardinality Janko4.LocalStructure
open Janko4.OuterReduction.OddIndex
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four

private theorem no_rankOne_order_168 {Y : Type*} [Group Y] [Finite Y]
    (hm : ChapterF.Source.IsRankOneModel Y) (hns : ¬ Group.IsSolvable Y)
    (hd : Nat.card Y ∣ 168) : False := by
  rcases hm.mathieu_section hns (hd.trans (by decide)) with hm | hm
  all_goals
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have heven : Even (Nat.card F) := by rw [hF]; decide
    have hchar : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
      simpa only [←Nat.card_eq_fintype_card] using Nat.even_iff.mp heven)
    have htwo : CharP F 2 := hchar ▸ inferInstance
    let := htwo
    have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1),mul_one,hF,←Nat.card_congr e.toEquiv] at hc
    rw [hc] at hd
    norm_num at hd

private theorem small_action {Y E : Type*} [Group Y] [Finite Y] [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ localCComponents S) [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B))
    (hE : Nat.card E ≤ 8) (f : B →* MulAut E) : f = 1 := by
  let B' := B.subgroupOf (B ⊔ (S : Subgroup Y))
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup Y) from le_sup_left)
  let a := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsSimpleGroup (B' ⧸ pCore 2 B') := a.isSimpleGroup
  let := hl.perfect
  let g := f.comp e.toMonoidHom
  by_contra hf
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
  let b := PerfectCoreTwoExtension.solvableKernelQuotientEquiv g.rangeRestrict g.rangeRestrict_surjective
  have hd : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card (MulAut E) := by
    rw [←Nat.card_congr a.toEquiv,Nat.card_congr b.toEquiv]
    exact (card_quotient_dvd_card _).trans g.range.card_subgroup_dvd_card
  have h168 : Nat.card (MulAut E) ∣ 168 := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa [←hk] using hE)
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E k hk]
    interval_cases k <;> norm_num [Fin.prod_univ_succ]
  let : Group.IsPerfect B := local_perfect hl
  let : Group.IsPerfect (B ⧸ pCore 2 B) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact no_rankOne_order_168 hm (Group.IsPerfect.not_isSolvable _) (hd.trans h168)

private theorem four_of_mathieu_surjection {Y : Type*} [Group Y] [Finite Y]
    {Z : Type*} [Group Z] [Finite Z]
    (q : Y →* Z) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B))
    (he : Nonempty (Z ≃* Sporadic.Mathieu.M22) ∨ Nonempty (Z ≃* Sporadic.Mathieu.M23) ∨
      Nonempty (Z ≃* Sporadic.Mathieu.M24)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  let := local_perfect hl
  let f := q.subgroupMap B
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (q.subgroupMap B).ker
    rw [ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap q.ker) (fun x y hh => Subtype.ext (Subtype.ext
        (congrArg (fun z : q.ker => (z : Y)) hh)))
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective B)
  exact (ChapterF.Source.MathieuLocal.rankOne_quotient_four (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono hn).trans (le_normalizer_map q)) (hm.of_equiv e.symm) he).of_mulEquiv e

private theorem max1_four (S : Sylow 2 M) (B : Subgroup M)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup M) ≤ normalizer (B : Set M))
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  let K := localKernel matrixA_mul_self matrixB_pow_four
  let e := localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
  let q := e.toMonoidHom.comp (QuotientGroup.mk' K)
  let : Group.IsSolvable q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    let : Group.IsNilpotent K := (IsElementaryAbelian.isPGroup 2 K).isNilpotent
    infer_instance
  exact four_of_mathieu_surjection q (e.surjective.comp (QuotientGroup.mk'_surjective _))
    S B hl hn hm (.inr (.inr ⟨MulEquiv.refl _⟩))

private theorem first_four (S : Sylow 2 InvolutionCentralizers.First.centralizer)
    (B : Subgroup InvolutionCentralizers.First.centralizer)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup InvolutionCentralizers.First.centralizer) ≤
      normalizer (B : Set InvolutionCentralizers.First.centralizer))
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
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
  let : IsSimpleGroup (B.subgroupOf H ⧸ pCore 2 (B.subgroupOf H)) := e.isSimpleGroup
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
  exact (four_of_mathieu_surjection mathieuProjection mathieuProjection_surjective P
    (B.subgroupOf H) hBP hn' (hm.of_equiv e) (.inl ⟨MulEquiv.refl _⟩)).of_mulEquiv e.symm

private theorem core_ne_bot (S : Sylow 2 Model) (B : Subgroup Model)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B)) : pCore 2 B ≠ ⊥ := by
  intro hc
  let e : B ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc).symm
  let : IsSimpleGroup B := e.isSimpleGroup
  let := local_perfect hl
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
    (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic S) hl hn
  have hr := JankoRank.eleven_le_automorphism_rank (MulEquiv.refl _) S B hn hfaith
  have hd := B.card_subgroup_dvd_card
  rw [Cardinality.model_card] at hd
  exact JankoRank.not_bender_of_janko_order hd hr
    (Chapter2.BenderFusion.GoodCentralizers.classificationModel_of_simpleBender
      ((hm.of_equiv e).simple_bender (Group.IsPerfect.not_isSolvable B)))

private noncomputable def markedSylow : Sylow 2 Model :=
  twoSubgroup_isPGroup.toSylow (by
    rw [twoSubgroup,index_map_subtype,localTwoSubgroup_index]
    exact Nat.Prime.not_dvd_mul Nat.prime_two (by decide)
      Janko4.OuterReduction.max1_odd_index_unconditional)

private theorem fixed_four (B : Subgroup Model)
    (hl : B ∈ localCComponents markedSylow)
    (hn : twoSubgroup ≤ normalizer (B : Set Model))
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  obtain ⟨N,hN,hBN,hSN⟩ := exists_maximal_two_local markedSylow B hn
    (core_ne_bot markedSylow B hl hn hm)
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
    let : IsSimpleGroup (B.subgroupOf M ⧸ pCore 2 (B.subgroupOf M)) := e.isSimpleGroup
    exact (max1_four (markedSylow.subtype (le_sup_right.trans hmax)) (B.subgroupOf M)
      (local_restrict hl hBM) (by rw [←subgroupOf_normalizer_eq hBM]; exact comap_mono hn)
      (hm.of_equiv e)).of_mulEquiv e.symm
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
      let : IsSimpleGroup ((B.subgroupOf C).map e.toMonoidHom ⧸
          pCore 2 ((B.subgroupOf C).map e.toMonoidHom)) := (c.symm.trans a).isSimpleGroup
      let : Group.IsSolvable e.toMonoidHom.ker := by
        rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
      have hnC : ((markedSylow.subtype hSC) : Subgroup C) ≤ normalizer (B.subgroupOf C : Set C) := by
        rw [←subgroupOf_normalizer_eq hBC]; exact comap_mono hn
      exact (first_four ((markedSylow.subtype hSC).mapSurjective e.surjective)
        ((B.subgroupOf C).map e.toMonoidHom)
        (Chapter1.Section02.localCComponents_map_of_solvable_ker (local_restrict hl hBC) e.toMonoidHom)
        ((map_mono hnC).trans (le_normalizer_map e.toMonoidHom))
        (hm.of_equiv (c.symm.trans a))).of_mulEquiv (a.symm.trans c)
    · have hd := (show 2^21 ∣ Nat.card markedSylow by rw [ambient_sylow_card]).trans
        (card_dvd_of_le hSC)
      rw [Nat.card_congr he.some.toEquiv,InvolutionCentralizers.Second.ambient_card] at hd
      norm_num at hd

/-- A full-Sylow-normalized local rank-one section in the actual J₄ carrier
has PSL₂(4) intrinsic two-core quotient. -/
theorem right_quotient_four {Y : Type*} [Group Y] [Finite Y]
    (e : Y ≃* Model) (S : Sylow 2 Y) (B : Subgroup Y)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup Y) ≤ normalizer (B : Set Y))
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hm : ChapterF.Source.IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
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
  let : IsSimpleGroup (B.map f.toMonoidHom ⧸ pCore 2 (B.map f.toMonoidHom)) := a.symm.isSimpleGroup
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hn).trans (le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  exact (fixed_four (B.map f.toMonoidHom) hl' hn' (hm.of_equiv a.symm)).of_mulEquiv a

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime.JankoFourSections
