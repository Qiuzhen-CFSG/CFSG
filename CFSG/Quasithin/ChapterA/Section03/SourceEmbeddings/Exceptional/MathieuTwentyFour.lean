module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.FaithfulSylow
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.ModelSeparation
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even.CatalogueCoverage
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds
/-!
# The exceptional sections are excluded from M₂₄

For nontrivial intrinsic two-core, its characteristic image gives a common
two-local overgroup of the original component and its full Sylow actor.
The checked normal-elementary catalogue places that overgroup inside an
octad, trio or sextet stabilizer. Trio and sextet orders exclude20160.
The actual octad quotient maps onto A₈ with a two-group kernel; perfection
preserves the exceptional section through that kernel. Its order forces
it to exhaust A₈, contradicting the proved distinction of exceptional
models from PSL₄(2). Thus the two-core is trivial, and even characteristic
forces a faithful full-Sylow action on the exceptional simple carrier.
Its order divides256, contradicting the native M₂₄ Sylow order1024.

All quotient and subgroup maps are literal native maps; no generic
proper-embedding classification is assumed.
Source: Aschbacher–Smith A.3.12(14), pp.47–48, and13.6.27, p.934;
GLS3, Table5.3e for the three native local geometries.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
open LinearFourCore PairOvergroups PairOvergroups.QuotientConstruction
open scoped Pointwise
private theorem not_alt_section (D : Subgroup (alternatingGroup seedOctad.val))
    (h : IsModel (D ⧸ pCore 2 D)) : False := by
  classical
  let : Nontrivial seedOctad.val := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [seed_card]; decide)
  have hcard : Nat.card (alternatingGroup seedOctad.val) = 20160 := by
    rw [nat_card_alternatingGroup, seed_card]
    decide
  have ht : D = ⊤ := eq_top_of_card_le D h hcard.le
  let : IsSimpleGroup (alternatingGroup seedOctad.val) :=
    alternatingGroup.isSimpleGroup (by rw [seed_card]; decide)
  let eD : D ≃* alternatingGroup seedOctad.val := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsSimpleGroup D := eD.isSimpleGroup
  have hc : pCore 2 D = ⊥ :=
    (inferInstance : (pCore 2 D).Normal).eq_bot_or_eq_top.resolve_right (by
      intro he
      have hd := h.card_dvd
      rw [he] at hd
      have hh : Nat.card (D ⧸ (⊤ : Subgroup D)) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
      rw [hh] at hd
      norm_num at hd)
  let a : seedOctad.val ≃ Fin 8 := Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card, seed_card])
  let e := ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans
    (eD.trans (a.altCongrHom.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm))
  exact h.not_binaryFour ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ⟨e⟩⟩

private theorem not_seed_octad_section (D : Subgroup (octadStabilizer seedOctad))
    [Group.IsPerfect D] (h : IsModel (D ⧸ pCore 2 D)) : False := by
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
  exact not_alt_section (D.map f) (section_map D h f)

private theorem not_octad_section (B : Subgroup M24) [Group.IsPerfect B]
    (h : IsModel (B ⧸ pCore 2 B)) (O : Octad) (hBO : B ≤ octadStabilizer O) : False := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq O seedOctad
  have hs : octadStabilizer seedOctad = (octadStabilizer O).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 seedOctad.val = (MulAction.stabilizer M24 O.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let eO : octadStabilizer O ≃* octadStabilizer seedOctad :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)
  let D := (B.subgroupOf (octadStabilizer O)).map eO.toMonoidHom
  let eD : D ≃* B := (eO.subgroupMap (B.subgroupOf (octadStabilizer O))).symm.trans
    (subgroupOfEquivOfLe hBO)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := eD.symm.toMonoidHom) eD.symm.surjective
  exact not_seed_octad_section D (h.of_equiv (QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)))

private theorem trio_not_20160 : ¬ 20160 ∣ Nat.card (trioStabilizer standardTrio) := by
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
  have h5 : 5 ∣ 2 ^ n * 1008 := ((by decide : 5 ∣ 20160).trans (hc ▸ hd)).trans
    (Nat.mul_dvd_mul_left _ hi)
  have hb := ((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left h5
  norm_num at hb

private theorem candidate_not_20160 (k : Fin 2) :
    ¬ 20160 ∣ Nat.card (EvenCandidates.localGroup k) := by
  fin_cases k
  · change ¬ 20160 ∣ Nat.card (EvenCandidates.localGroup 0)
    rw [Nat.card_congr EvenCatalogue.NormalSeeds.trioNormalizerEquiv.toEquiv]
    exact trio_not_20160
  · change ¬ 20160 ∣ Nat.card (EvenCandidates.localGroup 1)
    rw [Nat.card_congr EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toEquiv,
      SextetCore.stabilizer_card]
    decide

private noncomputable def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card, m24_order]
    decide +kernel)

private theorem fixed_core_eq_bot (B : Subgroup M24) [Group.IsPerfect B]
    (hn : SylowNormalizer.candidate ≤ normalizer (B : Set M24))
    (h : IsModel (B ⧸ pCore 2 B)) : pCore 2 B = ⊥ := by
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
  rw [he] at hBN
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · exact not_octad_section B h O (hBN.trans hO)
  · exact candidate_not_20160 k ((section_card_dvd h).trans (card_dvd_of_le (hBN.trans hk)))

private theorem fixed_not_section (B : Subgroup M24)
    (hB : B ∈ localCComponents markedSylow)
    (hn : (markedSylow : Subgroup M24) ≤ normalizer (B : Set M24))
    (h : IsModel (B ⧸ pCore 2 B)) : False := by
  let := local_perfect hB
  have hc := fixed_core_eq_bot B hn h
  have hs := sylow_card_dvd_of_core_eq_bot markedSylow B hB hn h hc
    (MainConverse.m24_evenCharacteristic markedSylow)
  change Nat.card SylowNormalizer.candidate ∣ 256 at hs
  rw [SylowNormalizer.candidate_card] at hs
  norm_num at hs

variable {G : Type*} [Group G] [Finite G]
/-- The literal Sylow-normalized exceptional source section cannot occur
in the M₂₄ model. -/
theorem not_mathieu_twentyFour (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* M24) : False := by
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

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
