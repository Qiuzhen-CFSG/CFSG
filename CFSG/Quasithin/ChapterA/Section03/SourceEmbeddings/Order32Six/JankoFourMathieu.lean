module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
public import Theory.Mathieu.M24.LocalGeometry.SubnormalSextet
public import Theory.GroupTheory.PerfectSmallNormalizer

/-!
# Full A₆ two-core quotients in the Mathieu branch of J₄

A full-Sylow normalized local C-component of M₂₄ cannot have quotient A₆
by its intrinsic two-core. For a nontrivial core the genuine elementary
normalizer catalogue places the original pair in an octad, trio or sextet.
The first two rows are excluded by binary linear-four geometry and a
factor-five obstruction. In the sextet, the full normalizer has odd index
dividing three, since 360 divides the original component order. Perfection
then makes the component subnormal, and the nonsplit hexacode quotient
excludes its order-360 core quotient. For trivial core, faithful Sylow action
contradicts the native orders of M₂₄ and Aut(A₆).

The J₄ max1 application uses this independently of the size of the image
core. Source: Aschbacher–Smith A.3.12 and 8.2.13, pp.47–48,722–723;
GLS3 Table 5.3e and the native sextet calculation in 2.3.9(7), p.526.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFour
open FiveLocalFF.SolvableQuotients LinearFourCore PairOvergroups PairOvergroups.QuotientConstruction

private theorem not_equiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hH : ∀ (T : Sylow 2 H) (D : Subgroup H), D ∈ localCComponents T →
      (T : Subgroup H) ≤ normalizer (D : Set H) →
      (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 6) → False) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  let d := e.subgroupMap B
  let q := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  exact hH (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)
    ((map_mono hn).trans (B.le_normalizer_map e.toMonoidHom))
    (q.symm.trans eB)

private theorem seed_octad_not_six (S : Sylow 2 (octadStabilizer seedOctad))
    (B : Subgroup (octadStabilizer seedOctad)) (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let a : seedOctad.val ≃ Fin 8 := Fintype.equivFinOfCardEq (by
    rw [←Nat.card_eq_fintype_card,seed_card])
  let e := a.altCongrHom.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm
  let q := e.toMonoidHom.comp alternatingAction
  have hq : Function.Surjective q := e.surjective.comp alternatingAction_surjective
  have hk : q.ker = (action seedOctad).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    ext x
    change alternatingAction x = 1 ↔ action seedOctad x = 1
    simp only [Subtype.ext_iff,alternatingAction_coe,Subgroup.coe_one]
  have hp : IsPGroup 2 q.ker := by
    rw [hk,←seed_core_eq_kernel]
    exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]; exact hp.comap_subtype
  let b := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hkb
  exact SixLocalFF.BinaryLinear.not_section_psl_four (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q) (b.symm.trans eB)

private theorem octad_not_six (O : Octad) (S : Sylow 2 (octadStabilizer O))
    (B : Subgroup (octadStabilizer O)) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup (octadStabilizer O)) ≤ normalizer (B : Set (octadStabilizer O)))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨g,hg⟩ := exists_smul_octad_eq O seedOctad
  let e : octadStabilizer O ≃* octadStabilizer seedOctad :=
    MulAction.stabilizerEquivStabilizer (G := M24) hg.symm
  exact not_equiv e S B hl hn eB (fun T D hd _ ed => seed_octad_not_six T D hd ed)

private theorem sextet_not_six (S : Sylow 2 (sextetStabilizer standardSextet))
    (B : Subgroup (sextetStabilizer standardSextet)) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup (sextetStabilizer standardSextet)) ≤
      normalizer (B : Set (sextetStabilizer standardSextet)))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let := local_perfect hl
  have hquot : Nat.card (B ⧸ pCore 2 B) = 360 := by
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hd360 : 360 ∣ Nat.card B := hquot ▸ card_quotient_dvd_card (pCore 2 B)
  have hiB : B.index ∣ 384 := by
    obtain ⟨k,hk⟩ := hd360
    have hh := B.card_mul_index
    rw [hk,SextetCore.stabilizer_card] at hh
    refine ⟨k,?_⟩
    nlinarith
  have hi : (normalizer (B : Set (sextetStabilizer standardSextet))).index ≤ 4 := by
    have hd := (index_dvd_of_le B.le_normalizer).trans hiB
    have h2 : ¬ 2 ∣ (normalizer (B : Set (sextetStabilizer standardSextet))).index :=
      fun h => S.not_dvd_index (h.trans (index_dvd_of_le hn))
    have hcop : Nat.Coprime (normalizer (B : Set (sextetStabilizer standardSextet))).index (2^7) :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm.pow_right 7
    exact (Nat.le_of_dvd (by decide : 0 < 3) (hcop.dvd_of_dvd_mul_left hd)).trans (by decide)
  have hsub := isSubnormal_of_perfect_of_normalizer_index_le_four B hi
  have hp : IsPPerfect 2 B := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (B ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (B ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (B ⧸ N) inferInstance
  rcases subnormal_sextet_orders standardSextet B hsub hp with hh | ⟨hh,_⟩ | hh <;> omega

private theorem trio_not_six (B : Subgroup (trioStabilizer standardTrio))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let f := affineQuotient affineCoverage
  obtain ⟨n,hn⟩ := (affineQuotient_kernel_isPGroup affineCoverage).exists_card_eq
  have hh := f.ker.card_mul_index
  rw [index_ker,hn] at hh
  have hi : Nat.card f.range ∣ 1008 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [Nat.card_prod,Matrix.PSL3Two.card_SL] at hd
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
      show Nat.factorial 3 = 6 from rfl] using hd
  have h5 : 5 ∣ Nat.card (trioStabilizer standardTrio) :=
    (show 5 ∣ Nat.card B from by
      have hc : Nat.card (B ⧸ pCore 2 B) = 360 := by
        rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup]
        norm_num
      exact (by decide : 5 ∣ 360).trans (hc ▸ card_quotient_dvd_card (pCore 2 B))).trans B.card_subgroup_dvd_card
  have hd : 5 ∣ 2^n * 1008 := (hh ▸ h5).trans (Nat.mul_dvd_mul_left _ hi)
  have hb := ((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left hd
  norm_num at hb

private theorem candidate_not_six (k : Fin 2)
    (S : Sylow 2 (EvenCandidates.localGroup k)) (B : Subgroup (EvenCandidates.localGroup k))
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup (EvenCandidates.localGroup k)) ≤
      normalizer (B : Set (EvenCandidates.localGroup k)))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  fin_cases k
  · exact not_equiv EvenCatalogue.NormalSeeds.trioNormalizerEquiv S B hl hn eB
      (fun _ D _ _ ed => trio_not_six D ed)
  · exact not_equiv EvenCatalogue.NormalSeeds.sextetNormalizerEquiv S B hl hn eB sextet_not_six

private def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card,m24_order]
    decide +kernel)

private theorem fixed_not_six (B : Subgroup M24)
    (hl : B ∈ localCComponents markedSylow)
    (hn : (markedSylow : Subgroup M24) ≤ normalizer (B : Set M24))
    (hne : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨N,hN,hBN,hSN⟩ := exists_maximal_two_local markedSylow B hn hne
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  obtain ⟨i,hi⟩ := MainConverse.M24Even.normalElementaryCatalogue R hR hnR heR
  have he : N = EvenCatalogue.localGroup i := by rw [hNR,hi]; rfl
  rw [he] at hBN hSN
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · have hBO := hBN.trans hO
    let d := subgroupOfEquivOfLe hBO
    apply octad_not_six O (markedSylow.subtype (hSN.trans hO))
      (B.subgroupOf (octadStabilizer O)) (local_restrict hl hBO) ?_
      ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)
    rw [←subgroupOf_normalizer_eq hBO]
    exact comap_mono hn
  · have hBK := hBN.trans hk
    let d := subgroupOfEquivOfLe hBK
    apply candidate_not_six k (markedSylow.subtype (hSN.trans hk))
      (B.subgroupOf (EvenCandidates.localGroup k)) (local_restrict hl hBK) ?_
      ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)
    rw [←subgroupOf_normalizer_eq hBK]
    exact comap_mono hn

/-- The native three-row exclusion with a nontrivial original two-core. -/
private theorem not_mathieu_twenty_four_of_core {G : Type*} [Group G] [Finite G]
    (e : G ≃* M24) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hne : pCore 2 B ≠ ⊥)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 Q markedSylow
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (markedSylow : Subgroup M24) := by
    have he := congrArg (fun P : Sylow 2 M24 => (P : Subgroup M24)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext x; rfl
    rw [hf,←map_map]
    exact he
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [f.toMonoidHom.ker_eq_bot f.injective]
    infer_instance
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f.toMonoidHom
  have hn' := (map_mono (f := f.toMonoidHom) hn).trans (B.le_normalizer_map f.toMonoidHom)
  rw [hS] at hl' hn'
  let b := B.equivMapOfInjective f.toMonoidHom f.injective
  have hc' : pCore 2 (B.map f.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hne
    apply (map_eq_bot_iff_of_injective (f := b.toMonoidHom) _ b.injective).mp
    rw [pCore_map_iso 2 b,hz]
  exact fixed_not_six (B.map f.toMonoidHom) hl' hn' hc'
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB)

/-- A full-Sylow normalized local C-component in M24 cannot have full A6
quotient by its intrinsic two-core, regardless of the size of that core. -/
theorem mathieu_not_six_section (S : Sylow 2 M24) (B : Subgroup M24)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup M24) ≤ normalizer (B : Set M24))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  by_cases hc : pCore 2 B = ⊥
  · let e := QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans eB)
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup B := e.isSimpleGroup
    let := local_perfect hl
    have hz : center B = ⊥ :=
      (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
        (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
    let : IsQuasisimple B :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
    have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
      (MainConverse.m24_evenCharacteristic S) hl hn
    let f := B.normalizerMonoidHom.comp (inclusion hn)
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply eq_bot_iff.mpr
      intro x hx
      apply Subtype.ext
      apply mem_bot.mp
      rw [←hfaith]
      refine ⟨x.property,?_⟩
      change inclusion hn x ∈ B.normalizerMonoidHom.ker at hx
      rwa [normalizerMonoidHom_ker] at hx
    have hd := card_dvd_of_injective f hf
    rw [Nat.card_congr (MulAut.congr e).toEquiv,AlternatingSix.ShadowLocal.card_aut] at hd
    have h64 : 2^6 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by
      rw [m24_order]
      norm_num)
    exact (by decide : ¬ 64 ∣ 1440) (h64.trans hd)
  · exact not_mathieu_twenty_four_of_core (MulEquiv.refl _) S B hl hn hc eB

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.JankoFour
