module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even.CatalogueCoverage
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalSeeds.NativeNormalizers
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The M24 local alternating-five section exclusion

The nontrivial two-core of the original local component gives a common
maximal two-local overgroup with its normalizing full Sylow. The native
normal-elementary catalogue puts that overgroup inside an octad, sextet or
trio stabilizer. Their literal quotients are PSL4(2), S6 and a group of
order prime to five, respectively. Solvable kernels preserve the original
perfect A5 section, so each native local geometry excludes it. No natural
or deleted module recognition is required.

Source: Aschbacher–Smith A.3.12(14), printed pp.47–48, in the point-component
inspection of 10.2.9, printed pp.751–752; GLS3 Table 5.3e.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
open SolvableQuotients LinearFourCore PairOvergroups PairOvergroups.QuotientConstruction

private theorem seed_octad_not_section (S : Sylow 2 (octadStabilizer seedOctad))
    (B : Subgroup (octadStabilizer seedOctad)) (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  classical
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
  let : Group.IsSolvable q.ker := by
    rw [hk,←seed_core_eq_kernel]
    let : Group.IsNilpotent (pCore 2 (octadStabilizer seedOctad)) := pCore_isPGroup.isNilpotent
    infer_instance
  exact binary_four_quotient_not_section q hq S B hl eB

private theorem octad_not_section (O : Octad) (S : Sylow 2 (octadStabilizer O))
    (B : Subgroup (octadStabilizer O)) (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨g,hg⟩ := exists_smul_octad_eq O seedOctad
  let e : octadStabilizer O ≃* octadStabilizer seedOctad :=
    MulAction.stabilizerEquivStabilizer (G := M24) hg.symm
  exact not_section_of_equiv e S B hl eB seed_octad_not_section

private theorem sextet_not_section (S : Sylow 2 (sextetStabilizer standardSextet))
    (B : Subgroup (sextetStabilizer standardSextet)) (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let : Group.IsSolvable SextetCore.columnHom.ker := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rw [SextetCore.columnHom_kernel_card] at hd
    have hh : p ∣ 2^6 * 3 := hd
    rcases hp.dvd_mul.mp hh with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  exact symmetric_six_quotient_not_section SextetCore.columnHom
    SextetCore.columnHom_surjective S B hl eB

private theorem trio_not_section (B : Subgroup (trioStabilizer standardTrio))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let f := affineQuotient affineCoverage
  obtain ⟨n,hn⟩ := (affineQuotient_kernel_isPGroup affineCoverage).exists_card_eq
  have hc := f.ker.card_mul_index
  rw [index_ker,hn] at hc
  have hi : Nat.card f.range ∣ 1008 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [Nat.card_prod,Matrix.PSL3Two.card_SL] at hd
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
      show Nat.factorial 3 = 6 from rfl] using hd
  have h5 := (five_dvd_card B eB).trans B.card_subgroup_dvd_card
  have hd : 5 ∣ 2^n * 1008 := (hc ▸ h5).trans (Nat.mul_dvd_mul_left _ hi)
  have hh := ((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left hd
  norm_num at hh

private theorem candidate_not_section (k : Fin 2)
    (S : Sylow 2 (EvenCandidates.localGroup k)) (B : Subgroup (EvenCandidates.localGroup k))
    (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  fin_cases k
  · apply not_section_of_equiv EvenCatalogue.NormalSeeds.trioNormalizerEquiv S B hl eB
    intro _ A _ eA
    exact trio_not_section A eA
  · exact not_section_of_equiv EvenCatalogue.NormalSeeds.sextetNormalizerEquiv S B hl eB
      sextet_not_section

private noncomputable def markedSylow : Sylow 2 M24 :=
  Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card,m24_order]
    decide +kernel)

private theorem fixed_not_section (B : Subgroup M24)
    (hl : B ∈ localCComponents markedSylow)
    (hn : (markedSylow : Subgroup M24) ≤ normalizer (B : Set M24))
    (hc : pCore 2 B ≠ ⊥) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨N,hN,hBN,hSN⟩ := exists_maximal_two_local markedSylow B hn hc
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le markedSylow hN hSN
  obtain ⟨i,hi⟩ := MainConverse.M24Even.normalElementaryCatalogue R hR hnR heR
  have he : N = EvenCatalogue.localGroup i := by rw [hNR,hi]; rfl
  rw [he] at hBN hSN
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · have hBO := hBN.trans hO
    let d := subgroupOfEquivOfLe hBO
    exact octad_not_section O (markedSylow.subtype (hSN.trans hO))
      (B.subgroupOf (octadStabilizer O)) (local_restrict hl hBO)
      ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)
  · have hBK := hBN.trans hk
    let d := subgroupOfEquivOfLe hBK
    exact candidate_not_section k (markedSylow.subtype (hSN.trans hk))
      (B.subgroupOf (EvenCandidates.localGroup k)) (local_restrict hl hBK)
      ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eB)

/-- M24 excludes the literal local A5 section whenever its two-core is nontrivial. -/
theorem not_section {G : Type*} [Group G] [Finite G]
    (e : G ≃* M24) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hc : pCore 2 B ≠ ⊥) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
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
  have hc' : pCore 2 (B.map f.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := (f.subgroupMap B).toMonoidHom) _
      (f.subgroupMap B).injective).mp
    rw [pCore_map_iso]
    exact hz
  exact fixed_not_section (B.map f.toMonoidHom) hl' hn' hc'
    (section_map f.toMonoidHom B hl eB).some

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
