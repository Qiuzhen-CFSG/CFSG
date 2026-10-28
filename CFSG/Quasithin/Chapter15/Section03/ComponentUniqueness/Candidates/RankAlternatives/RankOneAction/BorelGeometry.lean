module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Components
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.MainConverse.RankOneLocal

/-!
# Identifying the invariant Borel with M ∩ L

The selected component is quasisimple. Source 15.3.11(8) gives its
center equal to its two-core; with the independently supplied trivial
two-core it is simple. The established concrete rank-one local geometry
then gives characteristic two for its Sylow normalizer. We transport
that intrinsic normalizer to the ambient Borel with the actual inclusion.

The local results in `Local` show that this Borel is Y₊S-invariant.
Source 15.3.33(1) puts it in M ∩ I, while uniqueness of the proper Sylow
overgroup gives the reverse inclusion M ∩ L ≤ B. Thus B = M ∩ L and,
by 15.3.11(4), B normalizes Y₊. No Borel characteristic-two premise remains
in the two model-specific identification theorems.

Source: Aschbacher--Smith, 15.3.11(8), 15.3.33(1), and the rank-one
paragraph of 15.3.37, printed pp.1123, 1134--1135. The concrete input is
F.1.3(1), transported by `MainConverse.RankOneLocal`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction

private theorem generalizedFitting_eq_twoCore_of_characteristicTwo
    {H : Type*} [Group H] [Finite H]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    generalizedFitting H = pCore 2 H := by
  apply le_antisymm
  · rw [generalizedFitting]
    refine sup_le ?_ ?_
    · rw [fitting_eq_sup_pCore]
      apply iSup_le
      intro p
      by_cases hp : p.1.1 = 2
      · rw [hp]
      · apply le_trans _ hc
        intro x hx y hy
        exact pCore_commute_of_ne 2 p.1.1 (Ne.symm hp) y hy x hx
    · apply sSup_le
      intro K hK
      rcases hK.normal_dichotomy (pCore 2 H) with hk | hk
      · exact hk
      · exact (commutator_eq_bot_iff_le_centralizer.mp hk).trans hc
  · exact (pCore_le_fitting H 2).trans (fitting_le_generalizedFitting H)

variable {G : Type*} [Group G] [Finite G] {Yplus S M I L : Subgroup G}

theorem Setup.component_simple (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥) : IsSimpleGroup L := by
  let e := subgroupOfEquivOfLe h.component_le
  have hc : pCore 2 (L.subgroupOf I) = ⊥ := by
    apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
    rw [pCore_map_iso, hcore]
  have hz : center (L.subgroupOf I) = ⊥ :=
    (component_center_eq_twoCore h.component hodd).trans hc
  let := h.component.2
  let : IsSimpleGroup ((L.subgroupOf I) ⧸ center (L.subgroupOf I)) := IsQuasisimple.simple
  exact (((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).trans e).symm.isSimpleGroup

private theorem borel_characteristicTwo_of_evenCharacteristic
    [IsSimpleGroup L] (hna : ¬ IsMulCommutative L)
    (he : IsEvenCharacteristic L)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hf : ChapterF.Source.RankOneSylowFacts P) :
    generalizedFitting (ChapterF.Source.borel L S) =
      pCore 2 (ChapterF.Source.borel L S) := by
  let B : Subgroup L := normalizer (P : Set L)
  have hne : (P : Subgroup L) ≠ ⊥ := by
    intro hp
    have hh := hf.proper
    change normalizer ((P : Subgroup L) : Set L) < ⊤ at hh
    rw [hp] at hh
    have ht : normalizer ((⊥ : Subgroup L) : Set L) = ⊤ :=
      (⊥ : Subgroup L).normalizer_eq_top
    exact hh.ne ht
  have hmax : IsMaximalTwoLocal B := by
    refine ⟨⟨P, hne, P.isPGroup', rfl⟩, ?_⟩
    intro N hN hBN
    exact hf.unique_maximal N ((P : Subgroup L).le_normalizer.trans hBN)
      (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple hna hN))
  have hc := he P B hmax (P : Subgroup L).le_normalizer
  have hmap : B.map L.subtype = ChapterF.Source.borel L S := by
    have hh : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
      rw [← hP]
      exact comap_map_eq_self_of_injective L.subtype_injective _
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [← hh, ← subgroupOf_normalizer_eq inf_le_right,
      subgroupOf, map_comap_eq, range_subtype]
    rfl
  let e : B ≃* ChapterF.Source.borel L S :=
    (B.equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact generalizedFitting_eq_twoCore_of_characteristicTwo
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hc)

omit [Finite G] in
private theorem component_nonabelian (h : Setup Yplus S M I L) :
    ¬ IsMulCommutative L := by
  intro ha
  let := ha
  exact h.component_nonsolvable (Group.isSolvable_of_comm (fun a b => mul_comm' a b))

theorem Setup.linear_borel_characteristicTwo (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    generalizedFitting (ChapterF.Source.borel L S) =
      pCore 2 (ChapterF.Source.borel L S) := by
  let := h.component_simple hodd hcore
  obtain ⟨P, hP⟩ := h.component_sylow
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := heven; omega
  exact borel_characteristicTwo_of_evenCharacteristic (component_nonabelian h)
    (MainConverse.psl2_evenCharacteristic (component_nonabelian h) hn2 hm)
    P hP ((ChapterF.Source.IsRankOneModel.linear n hn hm).rankOneSylowFacts P)

theorem Setup.unitary_borel_characteristicTwo (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    generalizedFitting (ChapterF.Source.borel L S) =
      pCore 2 (ChapterF.Source.borel L S) := by
  let := h.component_simple hodd hcore
  obtain ⟨P, hP⟩ := h.component_sylow
  have hn2 : 2 ≤ n := by obtain ⟨k, hk⟩ := heven; omega
  exact borel_characteristicTwo_of_evenCharacteristic (component_nonabelian h)
    (MainConverse.psu3_evenCharacteristic (component_nonabelian h) hn2 hm)
    P hP ((ChapterF.Source.IsRankOneModel.projective_unitary n hn hm).rankOneSylowFacts P)

theorem Setup.linear_borel_identification (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSL L 2 (2 ^ n)) :
    ChapterF.Source.borel L S = M ⊓ L ∧
      Yplus ⊔ S ≤ normalizer (ChapterF.Source.borel L S : Set G) ∧
      ChapterF.Source.borel L S ≤ normalizer (Yplus : Set G) :=
  h.rankOne_borel_identification (ChapterF.Source.IsRankOneModel.linear n hn hm)
    (h.linear_borel_characteristicTwo hodd hcore hn heven hm)

theorem Setup.unitary_borel_identification (h : Setup Yplus S M I L)
    (hodd : pPrimeCore 2 I = ⊥) (hcore : pCore 2 L = ⊥)
    {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) :
    ChapterF.Source.borel L S = M ⊓ L ∧
      Yplus ⊔ S ≤ normalizer (ChapterF.Source.borel L S : Set G) ∧
      ChapterF.Source.borel L S ≤ normalizer (Yplus : Set G) :=
  h.rankOne_borel_identification (ChapterF.Source.IsRankOneModel.projective_unitary n hn hm)
    (h.unitary_borel_characteristicTwo hodd hcore hn heven hm)

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
