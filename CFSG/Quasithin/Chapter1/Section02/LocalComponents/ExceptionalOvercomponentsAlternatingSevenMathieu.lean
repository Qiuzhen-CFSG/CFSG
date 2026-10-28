module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenSection
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyFour
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
/-!
# The M₂₂ and M₂₄ containing rows for an original A₇ section

The M₂₂ full-Sylow two-local orders are prime to seven. For M₂₄ the actual
normal-elementary catalogue places the pair in a trio, sextet or octad
stabilizer. The first two orders exclude A₇; the octad's literal binary
quotient is A₈, excluded by the full-Sylow PSL₄(2) theorem. With trivial
two-core, the faithful Sylow action on A₇ excludes both ambient carriers.
The central triple cover of M₂₂ descends by its actual central quotient.
Source: Aschbacher–Smith A.3.12(12,14), pp.47–48, and 1.2.8, pp.506–507.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenMathieu
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings AlternatingSevenSection
open Chapter1.Section02.LocalModels
open LinearFourCore PairOvergroups PairOvergroups.QuotientConstruction
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem section_card_dvd {B : Subgroup G}
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) :
    2520 ∣ Nat.card B := by
  have hc : Nat.card (B ⧸ pCore 2 B) = 2520 := by
    rw [Nat.card_congr h.some.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact hc ▸ card_quotient_dvd_card (pCore 2 B)

private theorem not_seed_octad_section (S : Sylow 2 (octadStabilizer seedOctad))
    (D : Subgroup (octadStabilizer seedOctad))
    (hl : D ∈ localCComponents S)
    (hn : (S : Subgroup (octadStabilizer seedOctad)) ≤ normalizer (D : Set _))
    (h : Nonempty ((D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 7))) : False := by
  let f := alternatingAction
  have hk : f.ker = pCore 2 (octadStabilizer seedOctad) := by
    rw [seed_core_eq_kernel]
    ext x
    change (alternatingAction x = 1) ↔ (action seedOctad x = 1)
    constructor
    · intro h
      simpa only [alternatingAction_coe, OneMemClass.coe_one] using congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      simpa only [alternatingAction_coe, OneMemClass.coe_one] using h
  let : Group.IsSolvable f.ker := by
    rw [hk]
    let : Group.IsNilpotent (pCore 2 (octadStabilizer seedOctad)) := pCore_isPGroup.isNilpotent
    infer_instance
  obtain ⟨_,hn',h'⟩ := local_section_map hl hn h f
  let a : seedOctad.val ≃ Fin 8 := Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card, seed_card])
  let e := a.altCongrHom.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm
  exact AlternatingSevenBinary.not_binaryFour
    (S.mapSurjective alternatingAction_surjective) (D.map f) hn' h'
    ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,⟨e⟩⟩

private theorem not_octad_section (S : Sylow 2 M24) (B : Subgroup M24)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup M24) ≤ normalizer (B : Set M24))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (O : Octad) (hBO : B ≤ octadStabilizer O)
    (hSO : (S : Subgroup M24) ≤ octadStabilizer O) : False := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq O seedOctad
  have hs : octadStabilizer seedOctad = (octadStabilizer O).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 seedOctad.val = (MulAction.stabilizer M24 O.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let eO : octadStabilizer O ≃* octadStabilizer seedOctad :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)
  let T := S.subtype hSO
  let D := B.subgroupOf (octadStabilizer O)
  have hlD : D ∈ localCComponents T := local_restrict hl hBO
  have hnD : (T : Subgroup (octadStabilizer O)) ≤ normalizer (D : Set _) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : M24)
  let eD := subgroupOfEquivOfLe hBO
  have hD : Nonempty ((D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 7)) :=
    ⟨(QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)).trans h.some⟩
  let : Group.IsSolvable eO.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr eO.injective]
    infer_instance
  obtain ⟨hl',hn',h'⟩ := local_section_map hlD hnD hD eO.toMonoidHom
  exact not_seed_octad_section (T.mapSurjective eO.surjective)
    (D.map eO.toMonoidHom) hl' hn' h'

private theorem trio_not_2520 : ¬ 2520 ∣ Nat.card (trioStabilizer standardTrio) := by
  let f := affineQuotient affineCoverage
  have hp := affineQuotient_kernel_isPGroup affineCoverage
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker, hn] at hc
  have hi : Nat.card f.range ∣ 1008 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [Nat.card_prod, Matrix.PSL3Two.card_SL] at hd
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 3 = 6 from rfl] using hd
  intro hd
  have h5 : 5 ∣ 2 ^ n * 1008 := ((by decide : 5 ∣ 2520).trans (hc ▸ hd)).trans
    (Nat.mul_dvd_mul_left _ hi)
  have hb := ((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left h5
  norm_num at hb

private theorem candidate_not_2520 (k : Fin 2) :
    ¬ 2520 ∣ Nat.card (EvenCandidates.localGroup k) := by
  fin_cases k
  · change ¬ 2520 ∣ Nat.card (EvenCandidates.localGroup 0)
    rw [Nat.card_congr EvenCatalogue.NormalSeeds.trioNormalizerEquiv.toEquiv]
    exact trio_not_2520
  · change ¬ 2520 ∣ Nat.card (EvenCandidates.localGroup 1)
    rw [Nat.card_congr EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toEquiv,
      SextetCore.stabilizer_card]
    decide

private noncomputable def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card, m24_order]
    decide +kernel)

private theorem fixed_core_eq_bot (B : Subgroup M24)
    (hB : B ∈ localCComponents markedSylow)
    (hn : SylowNormalizer.candidate ≤ normalizer (B : Set M24))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : pCore 2 B = ⊥ := by
  by_contra hc
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hloc : IsTwoLocal (normalizer (U : Set M24)) :=
    ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal hloc
  have hSN : (markedSylow : Subgroup M24) ≤ N := hn.trans (hnorm.trans hNN)
  have hBN : B ≤ N := B.le_normalizer.trans (hnorm.trans hNN)
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  obtain ⟨i,hi⟩ := MainConverse.M24Even.normalElementaryCatalogue R hR hnR heR
  have he : N = EvenCatalogue.localGroup i := by rw [hNR,hi]; rfl
  rw [he] at hBN hSN
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · exact not_octad_section markedSylow B hB hn h O (hBN.trans hO) (hSN.trans hO)
  · exact candidate_not_2520 k ((section_card_dvd h).trans (card_dvd_of_le (hBN.trans hk)))

private theorem fixed_not_section (B : Subgroup M24)
    (hB : B ∈ localCComponents markedSylow)
    (hn : (markedSylow : Subgroup M24) ≤ normalizer (B : Set M24))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) : False := by
  let := Exceptional.local_perfect hB
  have hc := fixed_core_eq_bot B hB hn h
  have hs := sylow_card_dvd_of_core_eq_bot markedSylow B hB hn h hc
    (MainConverse.m24_evenCharacteristic markedSylow)
  change Nat.card SylowNormalizer.candidate ∣ 16 at hs
  rw [SylowNormalizer.candidate_card] at hs
  norm_num at hs

/-- The literal Sylow-normalized A₇ source section cannot occur
in the M₂₄ model. -/
theorem not_mathieuTwentyFour (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7))) (e : G ≃* M24) : False := by
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 Q markedSylow
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (markedSylow : Subgroup M24) := by
    have he := congrArg (fun P : Sylow 2 M24 => (P : Subgroup M24)) hg
    change ((S : Subgroup G).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at he
    have hf : f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact MulEquiv.trans_apply e (MulAut.conj g) x
    rw [hf, ← Subgroup.map_map]
    exact he
  let : Group.IsSolvable f.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr f.injective]
    infer_instance
  obtain ⟨hl, hnorm, hm⟩ := local_section_map hB hn h f.toMonoidHom
  rw [hS] at hl hnorm
  exact fixed_not_section (B.map f.toMonoidHom) hl hnorm hm


/-- An original A₇ section cannot be normalized by a full Sylow in M₂₂. -/
theorem not_mathieuTwentyTwo (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (e : G ≃* M22) : False := by
  by_cases hc : pCore 2 B = ⊥
  · have hs := sylow_card_dvd_of_core_eq_bot S B hl hn h hc
      (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m22_evenCharacteristic S)
    have hd : 32 ∣ Nat.card G := by
      rw [Nat.card_congr e.toEquiv,m22_order]
      decide
    have hh := (S.pow_dvd_card_of_pow_dvd_card (n := 5) hd).trans hs
    norm_num at hh
  · let U := (pCore 2 B).map B.subtype
    have hU : U ≠ ⊥ := fun he => hc
      ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
    have hloc : IsTwoLocal (normalizer (U : Set G)) :=
      ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
    have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
    have hSN : (S : Subgroup G) ≤ normalizer (U : Set G) := hn.trans hnorm
    have hBN : B ≤ normalizer (U : Set G) := B.le_normalizer.trans hnorm
    let N := (normalizer (U : Set G)).map e.toMonoidHom
    have hN : IsTwoLocal N := Theory.Quasithin.isTwoLocal_map e hloc
    have hSN' : (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup M22) ≤ N := map_mono (f := e.toMonoidHom) hSN
    have hb := M22TwoLocalOrders.not_seven_dvd_card_twoLocal (S.mapSurjective (f := e.toMonoidHom) e.surjective) N hN hSN'
    have hd : 7 ∣ Nat.card N := by
      rw [card_map_of_injective e.injective]
      exact ((by decide : 7 ∣ 2520).trans (section_card_dvd h)).trans (card_dvd_of_le hBN)
    exact hb hd

/-- The genuine central triple cover also excludes the A₇ section: the
same original pair maps through the actual central quotient. -/
theorem not_mathieuTwentyTwo_cover (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hm : IsM22Cover G) : False := by
  obtain ⟨_,_,⟨e⟩⟩ := hm
  let q := QuotientGroup.mk' (center G)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext
      (mem_center_iff.mp a.property b).symm)
  obtain ⟨hl',hn',h'⟩ := local_section_map hl hn h q
  exact not_mathieuTwentyTwo (S.mapSurjective (QuotientGroup.mk'_surjective (center G)))
    (B.map q) hl' hn' h' e

/-- The two unwanted simple Mathieu quotients of the literal containing
local subgroup are excluded without any global embedding-list hypothesis. -/
theorem local_overcomponent_not_mathieuTwentyTwo_or_Four
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* M22) ∧
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* M24) := by
  constructor
  · rintro ⟨e⟩
    exact not_model_of_local_overcomponent not_mathieuTwentyTwo T hX hn hK hXK h e
  · rintro ⟨e⟩
    exact not_model_of_local_overcomponent not_mathieuTwentyFour T hX hn hK hXK h e

/-- The actual containing quotient cannot be the genuine three-cover of
M₂₂; this does not identify a quasisimple group with its central quotient. -/
theorem local_overcomponent_not_mathieuTwentyTwo_cover
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ IsM22Cover (K ⧸ pCore 2 K) := by
  obtain ⟨S,B,hl,hs,hm⟩ := local_overcomponent_pair T hX hn hK hXK h
  exact not_mathieuTwentyTwo_cover S B hl hs hm

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenMathieu
