module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Held excludes a local alternating-five section with nontrivial two-core

The original two-core places the smaller component and its normalizing full
Sylow in a common maximal two-local. The native maximal-normalizer catalogue
reduces this to max3, max4 or max5. The first two have literal surjections to
S6 with solvable kernels: after the intrinsic two-core, the remaining kernel
has order dividing three. The last has order prime to five. Each contradicts
the same A5 two-core quotient of the original local component.

Source: Aschbacher–Smith A.3.12(19), printed pp.47–48, used in 10.2.9,
printed pp.751–752; the native two-local geometry is GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
open SolvableQuotients
open _root_.Held.LocalPairs.PairCoverage
open _root_.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

private theorem max34_not_section (i : Bool)
    (S : Sylow 2 (localOvergroup i)) (B : Subgroup (localOvergroup i))
    (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  let q := localQuotientMap i
  let f := SixPoint.quotientAction i
  have hp : IsPGroup 3 f.ker := isPGroup_iff_card_dvd_pow.mpr
    ⟨1, by simpa only [pow_one] using
      _root_.Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i⟩
  let : Group.IsNilpotent f.ker := hp.isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  let : Group.IsSolvable q.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 (localOvergroup i))).ker
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 (localOvergroup i)) := pCore_isPGroup.isNilpotent
    infer_instance
  let : Group.IsSolvable (f.comp q).ker := by
    change Group.IsSolvable (f.ker.comap q)
    exact isSolvable_comap_of_solvable_ker q f.ker
  exact symmetric_six_quotient_not_section (f.comp q)
    ((SixPoint.quotientAction_surjective i).comp (QuotientGroup.mk'_surjective _)) S B hl eB

private theorem candidate_not_section (i : Fin 3)
    (S : Sylow 2 (_root_.Held.TwoLocalCandidates.subgroup i))
    (B : Subgroup (_root_.Held.TwoLocalCandidates.subgroup i))
    (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  fin_cases i
  · exact max34_not_section false S B hl eB
  · exact max34_not_section true S B hl eB
  · have hd := (five_dvd_card B eB).trans B.card_subgroup_dvd_card
    change 5 ∣ Nat.card _root_.Held.TwoLocalCandidates.max5 at hd
    rw [_root_.Held.InvolutionFixedData.TwoB.max5_card] at hd
    norm_num at hd

private theorem fixed_not_section (T : Sylow 2 _root_.Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map (T : Subgroup _root_.Held.He).subtype : Set _root_.Held.He)) →
      ∃ (i : Fin 3) (g : _root_.Held.He),
        normalizer (R.map (T : Subgroup _root_.Held.He).subtype : Set _root_.Held.He) =
          (_root_.Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (B : Subgroup _root_.Held.He) (hl : B ∈ localCComponents T)
    (hn : (T : Subgroup _root_.Held.He) ≤ normalizer (B : Set _root_.Held.He))
    (hc : pCore 2 B ≠ ⊥) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨N,hN,hBN,hTN⟩ := exists_maximal_two_local T B hn hc
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  have hN' : N = (_root_.Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom :=
    hNR.trans hg
  let d : N ≃* _root_.Held.TwoLocalCandidates.subgroup i :=
    (MulEquiv.subgroupCongr hN').trans ((MulAut.conj g).subgroupMap _).symm
  let a := subgroupOfEquivOfLe hBN
  exact not_section_of_equiv d (T.subtype hTN) (B.subgroupOf N) (local_restrict hl hBN)
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eB) (candidate_not_section i)

/-- The literal Held carrier excludes the normalized local A5 section with
nontrivial two-core, without any deleted-module hypothesis. -/
theorem not_section {G : Type*} [Group G] [Finite G]
    (e : G ≃* _root_.Held.He) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hc : pCore 2 B ≠ ⊥) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) : False := by
  obtain ⟨T,hcatalogue⟩ := _root_.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq _root_.Held.He Q T
  let f := e.trans (MulAut.conj g)
  have hS : (S : Subgroup G).map f.toMonoidHom = (T : Subgroup _root_.Held.He) := by
    have he := congrArg (fun P : Sylow 2 _root_.Held.He => (P : Subgroup _root_.Held.He)) hg
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
  exact fixed_not_section T hcatalogue (B.map f.toMonoidHom) hl' hn' hc'
    (section_map f.toMonoidHom B hl eB).some

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
