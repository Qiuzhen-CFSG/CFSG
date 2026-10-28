module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5PointComparison
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue

/-!
# Held excludes every original binary-three point configuration

The source's actual smaller component survives in I/Z(I) with its
SL₃(2) two-core quotient and is normalized by a full Sylow two-subgroup.
A common maximal two-local is conjugate to Held's max3, max4 or max5.
The first two are seven-free. In max5 the normalized subgroup is the whole
perfect group, whose two-core center is central. Transporting this back
contradicts the source's noncentral two-core center in the literal image.

No irreducibility or splitting of the selected module is assumed. In
particular, natural sections, fixed vectors and nonsplit extensions remain
included. Quasisimple.Source removes Held from its actual carrier list.
Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751;
GLS3 Table 5.3p for the native Held two-local geometry.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other

private theorem core_center_central_of_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K)
    (hc : (center (pCore 2 K)).map (pCore 2 K).subtype ≤ center K) :
    (center (pCore 2 H)).map (pCore 2 H).subtype ≤ center H := by
  let d : pCore 2 H ≃* pCore 2 K :=
    (e.subgroupMap (pCore 2 H)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  rintro _ ⟨z,hz,rfl⟩
  have hdz : d z ∈ center (pCore 2 K) := (centerCongr d ⟨z,hz⟩).property
  have hcz : e (z : H) ∈ center K := hc ⟨d z,hdz,rfl⟩
  have hh : e.symm (e (z : H)) ∈ center H :=
    (centerCongr e.symm ⟨e (z : H),hcz⟩).property
  simpa only [MulEquiv.symm_apply_apply,Subgroup.subtype_apply] using hh

open _root_.Held.LocalPairs.PairCoverage
open _root_.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
private theorem max34_seven_free (i : Bool) : ¬ 7 ∣ Nat.card (localOvergroup i) := by
  let f := SixPoint.quotientAction i
  have hk : ¬ 7 ∣ Nat.card f.ker := fun h =>
    (by decide : ¬ 7 ∣ 3) (h.trans (_root_.Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i))
  have hi : ¬ 7 ∣ Nat.card f.range := by
    intro h
    have hh := h.trans f.range.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh
  have hquot : ¬ 7 ∣ Nat.card (LocalQuotient i) := by
    rw [←f.ker.card_mul_index,index_ker]
    exact fun h => ((by decide : Nat.Prime 7).dvd_mul.mp h).elim hk hi
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := localOvergroup i)).exists_card_eq
  rw [←(pCore 2 (localOvergroup i)).card_mul_index,index_eq_card,hn]
  intro h
  rcases (by decide : Nat.Prime 7).dvd_mul.mp h with h | h
  · exact (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow h)
  · exact hquot h

private theorem candidate_core_center_central (i : Fin 3)
    (S : Sylow 2 (_root_.Held.TwoLocalCandidates.subgroup i))
    (B : Subgroup (_root_.Held.TwoLocalCandidates.subgroup i))
    (hn : (S : Subgroup (_root_.Held.TwoLocalCandidates.subgroup i)) ≤
      normalizer (B : Set (_root_.Held.TwoLocalCandidates.subgroup i)))
    (h168 : 168 ∣ Nat.card B) :
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  fin_cases i
  · exact (max34_seven_free false
      (((by decide : 7 ∣ 168).trans h168).trans B.card_subgroup_dvd_card)).elim
  · exact (max34_seven_free true
      (((by decide : 7 ∣ 168).trans h168).trans B.card_subgroup_dvd_card)).elim
  · have ht := _root_.Held.TwoLocalCandidates.max5_normalized_subgroup_top S B hn h168
    let e : B ≃* _root_.Held.TwoLocalCandidates.subgroup 2 :=
      (MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv
    exact core_center_central_of_equiv e _root_.Held.TwoLocalCandidates.max5_core_center_central

private theorem fixed_core_center_central (T : Sylow 2 _root_.Held.He)
    (hcatalogue : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      IsMaximalTwoLocal (normalizer (R.map (T : Subgroup _root_.Held.He).subtype : Set _root_.Held.He)) →
      ∃ (i : Fin 3) (g : _root_.Held.He),
        normalizer (R.map (T : Subgroup _root_.Held.He).subtype : Set _root_.Held.He) =
          (_root_.Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (B : Subgroup _root_.Held.He)
    (hn : (T : Subgroup _root_.Held.He) ≤ normalizer (B : Set _root_.Held.He))
    (hc : pCore 2 B ≠ ⊥) (h168 : 168 ∣ Nat.card B) :
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  obtain ⟨N,hN,hBN,hTN⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.exists_maximal_two_local T B hn hc
  obtain ⟨R,hR,hRn,hRe,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hRn hRe (hNR ▸ hN)
  have hN' : N = (_root_.Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom :=
    hNR.trans hg
  let d : N ≃* _root_.Held.TwoLocalCandidates.subgroup i :=
    (MulEquiv.subgroupCongr hN').trans ((MulAut.conj g).subgroupMap _).symm
  let B' := B.subgroupOf N
  let S := T.subtype hTN
  have hn' : (S : Subgroup N) ≤ normalizer (B' : Set N) := by
    rw [←subgroupOf_normalizer_eq hBN]
    exact comap_mono hn
  have hm : ((S : Subgroup N).map d.toMonoidHom) ≤ normalizer (B'.map d.toMonoidHom : Set _) :=
    (map_mono (f := d.toMonoidHom) hn').trans (le_normalizer_map d.toMonoidHom)
  have hd : 168 ∣ Nat.card (B'.map d.toMonoidHom) := by
    rw [card_map_of_injective d.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv ▸ h168
  have hcmp := candidate_core_center_central i
    (S.mapSurjective (f := d.toMonoidHom) d.surjective) (B'.map d.toMonoidHom) hm hd
  let e : B ≃* B'.map d.toMonoidHom :=
    (subgroupOfEquivOfLe hBN).symm.trans (d.subgroupMap B')
  exact core_center_central_of_equiv e hcmp

public theorem held_core_center_central (S : Sylow 2 _root_.Held.He) (B : Subgroup _root_.Held.He)
    (hn : (S : Subgroup _root_.Held.He) ≤ normalizer (B : Set _root_.Held.He))
    (hc : pCore 2 B ≠ ⊥) (h168 : 168 ∣ Nat.card B) :
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  obtain ⟨T,hcatalogue⟩ := _root_.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.exists_sylow_catalogue
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq _root_.Held.He S T
  let a := MulAut.conj g
  have hS : (S : Subgroup _root_.Held.He).map a.toMonoidHom = (T : Subgroup _root_.Held.He) := by
    exact congrArg (fun P : Sylow 2 _root_.Held.He => (P : Subgroup _root_.Held.He)) hg
  have hn' := (map_mono (f := a.toMonoidHom) hn).trans (B.le_normalizer_map a.toMonoidHom)
  rw [hS] at hn'
  have hc' : pCore 2 (B.map a.toMonoidHom) ≠ ⊥ := by
    intro hz
    apply hc
    apply (map_eq_bot_iff_of_injective (f := (a.subgroupMap B).toMonoidHom) _
      (a.subgroupMap B).injective).mp
    rw [pCore_map_iso]
    exact hz
  have hd : 168 ∣ Nat.card (B.map a.toMonoidHom) := by
    rwa [card_map_of_injective a.injective]
  exact core_center_central_of_equiv (a.subgroupMap B)
    (fixed_core_center_central T hcatalogue (B.map a.toMonoidHom) hn' hc' hd)


open scoped MatrixGroups
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The actual Held carrier is impossible on every original binary-three
module row. The source's fixed vectors and nonsplit extensions are retained. -/
public theorem not_held_of_binary_three [Group.IsPerfect I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (eI : (I ⧸ center I) ≃* _root_.Held.He) : False := by
  obtain ⟨S,_,_,hSN,_⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let A := (L.subgroupOf I).map (eI.toMonoidHom.comp q)
  let Q := R.mapSurjective (f := eI.toMonoidHom) eI.surjective
  have hQ : (Q : Subgroup _root_.Held.He) =
      (R : Subgroup (I ⧸ center I)).map eI.toMonoidHom := rfl
  have hn : (Q : Subgroup _root_.Held.He) ≤ normalizer (A : Set _root_.Held.He) := by
    have hh := (map_mono (f := eI.toMonoidHom) hSN).trans (le_normalizer_map eI.toMonoidHom)
    rw [hQ]
    simpa only [A,B,q,map_map] using hh
  have hnoncentral := marked_core_center_not_central D c.strict.le eI
  apply hnoncentral
  apply held_core_center_central Q A hn
  · intro hz
    apply hnoncentral
    rintro _ ⟨z,_,rfl⟩
    have he : (z : A) = 1 := mem_bot.mp (hz ▸ z.property)
    change (z : A) ∈ center A
    rw [he]
    exact one_mem _
  · let dA := (markedCoreQuotientEquiv D c.strict.le eI).symm.trans dL
    have hd : Nat.card (A ⧸ pCore 2 A) = 168 :=
      (Nat.card_congr dA.toEquiv).trans Matrix.PSL3Two.card_SL
    rw [←hd]
    exact card_quotient_dvd_card (pCore 2 A)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
