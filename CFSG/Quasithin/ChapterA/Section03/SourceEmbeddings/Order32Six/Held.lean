module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.Mathieu
public import Theory.SpecificGroups.Held.TwoLocalCandidates.AlternatingSix
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue

/-!
# Excluding Held for the order-32 alternating-six section

The original nontrivial two-core and its normalizing full Sylow place the
local component in a common maximal two-local. The native normalizer catalogue
reduces this to max3, max4 and max5. The first two exclude every perfect
subgroup with A₆ two-core quotient by the genuine nonsplit cubic extension;
max5 has order prime to five. The full source restriction then eliminates
Held from the remaining ordinary carriers, leaving only J₄.

Source: Aschbacher–Smith A.3.12, pp.47–48; GLS3 Table 5.3p and the actual
Held maximal-normalizer catalogue.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
open FiveLocalFF.SolvableQuotients
open _root_.Held.LocalPairs.PairCoverage
open _root_.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

private theorem held_not_equiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (S : Sylow 2 G) (B : Subgroup G) (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hH : ∀ (T : Sylow 2 H) (D : Subgroup H), D ∈ localCComponents T →
      (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 6) → False) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  let d := e.subgroupMap B
  exact hH (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans eB)

private theorem held_candidate_not_six (i : Fin 3)
    (S : Sylow 2 (_root_.Held.TwoLocalCandidates.subgroup i))
    (B : Subgroup (_root_.Held.TwoLocalCandidates.subgroup i))
    (hl : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  fin_cases i
  · exact @_root_.Held.TwoLocalCandidates.AlternatingSix.not_perfect_section false B
      (local_perfect hl) eB
  · exact @_root_.Held.TwoLocalCandidates.AlternatingSix.not_perfect_section true B
      (local_perfect hl) eB
  · have hd := (card_quotient_dvd_card (pCore 2 B)).trans B.card_subgroup_dvd_card
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup] at hd
    change Nat.factorial (Nat.card (Fin 6)) / 2 ∣ Nat.card _root_.Held.TwoLocalCandidates.max5 at hd
    rw [_root_.Held.InvolutionFixedData.TwoB.max5_card] at hd
    norm_num at hd

private theorem held_fixed_not_six (T : Sylow 2 _root_.Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map (T : Subgroup _root_.Held.He).subtype : Set _root_.Held.He)) →
      ∃ (i : Fin 3) (g : _root_.Held.He),
        normalizer (R.map (T : Subgroup _root_.Held.He).subtype : Set _root_.Held.He) =
          (_root_.Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (B : Subgroup _root_.Held.He) (hl : B ∈ localCComponents T)
    (hn : (T : Subgroup _root_.Held.He) ≤ normalizer (B : Set _root_.Held.He))
    (hc : pCore 2 B ≠ ⊥) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨N,hN,hBN,hTN⟩ := exists_maximal_two_local T B hn hc
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  have hN' : N = (_root_.Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom :=
    hNR.trans hg
  let d : N ≃* _root_.Held.TwoLocalCandidates.subgroup i :=
    (MulEquiv.subgroupCongr hN').trans ((MulAut.conj g).subgroupMap _).symm
  let a := subgroupOfEquivOfLe hBN
  exact held_not_equiv d (T.subtype hTN) (B.subgroupOf N) (local_restrict hl hBN)
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eB) (held_candidate_not_six i)

/-- The literal Held model excludes the full-Sylow normalized local A₆ section
with its original nontrivial two-core. -/
theorem not_held {G : Type*} [Group G] [Finite G]
    (e : G ≃* _root_.Held.He) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hc : pCore 2 B ≠ ⊥) (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : False := by
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
  let b := B.equivMapOfInjective f.toMonoidHom f.injective
  have hc' : pCore 2 (B.map f.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := b.toMonoidHom) _ b.injective).mp
    rw [pCore_map_iso]
    exact hz
  exact held_fixed_not_six T hcatalogue (B.map f.toMonoidHom) hl' hn' hc'
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB)

/-- Under the original source contract, the order-32 A₆ section leaves only
J₄. The native nonsplit cubic Held branch has no additional premise. -/
theorem remaining_jankoFour {G : Type*} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    Nonempty (K ≃* Janko4.Model) := by
  rcases remaining_jankoFour_or_held hG hO T hB hK hBK hTB hcore hA6 with he | he
  · exact he
  · obtain ⟨S,_,hl,hn,_,hc,ha⟩ := source_sylow_restriction T hB hK hBK hTB hcore hA6
    have hne : pCore 2 (B.subgroupOf K) ≠ ⊥ := by
      intro hz
      rw [hz,card_bot] at hc
      omega
    exact (not_held he.some S (B.subgroupOf K) hl hn hne ha.some).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
