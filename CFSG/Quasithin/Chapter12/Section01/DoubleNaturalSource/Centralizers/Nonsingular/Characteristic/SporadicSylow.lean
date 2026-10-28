module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.FourModels
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Rudvalis.Model.SylowElementarySixteen
public import Mathlib.GroupTheory.Schreier

/-!
# Excluding the Held and Rudvalis nonsingular components

In degree four the original moving subgroup has order64 and is normal in
an actual Sylow subgroup of the component. Its central quotient map is
injective. The certified Rudvalis normal-elementary catalogue has at most
five generators in every row, hence order at most32. In Held the two
normal-elementary rows of order64 have normalizers of order prime to
seven, while the original point residual retains its L3(2) two-core
quotient and normalizes the same moving subgroup. Both alternatives are
therefore impossible.

The calculations use the existing literal Sylow catalogues and quotient
maps. No new enumeration, model marking, ambient-Sylow premise or source
classification premise is assumed. `SporadicSource` applies both exclusions
to the actual nonsingular-centralizer and degree-five closure assembly.
Source: Aschbacher--Smith 12.1.1, printed p.788; GLS3 Tables5.3p and5.3r.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

private theorem elementary_closure_card_le {X : Type*} [Group X] [Finite X]
    (s : Finset X) [IsElementaryAbelian 2 (closure (s : Set X))] (hs : s.card ≤ 5) :
    Nat.card (closure (s : Set X)) ≤ 32 := by
  have hd : Nat.card (closure (s : Set X)) ∣ 2 ^ Group.rank (closure (s : Set X)) :=
    card_dvd_exponent_pow_rank' _
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _))
  exact (Nat.le_of_dvd (by positivity) hd).trans
    (Nat.pow_le_pow_right (by decide) ((Subgroup.rank_closure_finset_le_card s).trans hs))

open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover in
private theorem rudvalis_candidate_card_le (i : Fin 6)
    [IsElementaryAbelian 2 (elementary i)] : Nat.card (elementary i) ≤ 32 := by
  classical
  let c := elementaryGenerator
  let s : Fin 6 → Finset Rudvalis.Model :=
    ![{c 0},{c 0,c 1},{c 0,c 1,c 2},{c 0,c 1,c 2,c 3},
      {c 0,c 1,c 2,c 3,c 4},{c 0,c 1,c 2,c 3,c 5}]
  have heq : closure (s i : Set Rudvalis.Model) = elementary i := by
    fin_cases i <;> simp only [s, elementary, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Finset.coe_insert,Finset.coe_singleton]
    all_goals rfl
  let : IsElementaryAbelian 2 (closure (s i : Set Rudvalis.Model)) := heq.symm ▸ inferInstanceAs
    (IsElementaryAbelian 2 (elementary i))
  have hfive (a b c d e : Rudvalis.Model) : ({a,b,c,d,e} : Finset _).card ≤ 5 := by
    have := Finset.card_insert_le a {b,c,d,e}
    have := Finset.card_insert_le b {c,d,e}
    have := Finset.card_insert_le c {d,e}
    have := Finset.card_insert_le d {e}
    simp only [Finset.card_singleton] at *
    omega
  rw [←heq]
  apply elementary_closure_card_le
  fin_cases i
  · simp [s]
  · change ({c 0,c 1} : Finset Rudvalis.Model).card ≤ 5
    simpa only [Finset.insert_idem, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using hfive (c 0) (c 1) (c 1) (c 1) (c 1)
  · change ({c 0,c 1,c 2} : Finset Rudvalis.Model).card ≤ 5
    simpa only [Finset.insert_idem, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using hfive (c 0) (c 1) (c 2) (c 2) (c 2)
  · change ({c 0,c 1,c 2,c 3} : Finset Rudvalis.Model).card ≤ 5
    simpa only [Finset.insert_idem, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using hfive (c 0) (c 1) (c 2) (c 3) (c 3)
  · exact hfive _ _ _ _ _
  · exact hfive _ _ _ _ _

private theorem rudvalis_normal_elementary_bound (P : Sylow 2 Rudvalis.Model)
    (E : Subgroup P) (hn : E.Normal) (he : IsElementaryAbelian 2 E) : Nat.card E ≤ 32 := by
  let U := E.map (P : Subgroup Rudvalis.Model).subtype
  let := he
  let := hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hUP : U ≤ P := map_subtype_le E
  have hPN : (P : Subgroup Rudvalis.Model) ≤ normalizer (U : Set Rudvalis.Model) := by
    rintro _ hx
    exact le_normalizer_map (P : Subgroup Rudvalis.Model).subtype
      (mem_map_of_mem _ (show (⟨_,hx⟩ : P) ∈ normalizer (E : Set P) from le_normalizer_of_normal (mem_top _)))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Rudvalis.Model P Rudvalis.SylowInvariantPair.sylow
  let a := MulAut.conj g
  let W := U.map a.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hWP : W ≤ Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.localP := by
    have hh := map_mono (f := a.toMonoidHom) hUP
    change W ≤ (g • P : Sylow 2 Rudvalis.Model) at hh
    rwa [hg] at hh
  have hWN : Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.localP ≤
      normalizer (W : Set Rudvalis.Model) := by
    have hh := (map_mono (f := a.toMonoidHom) hPN).trans (le_normalizer_map a.toMonoidHom)
    change ((g • P : Sylow 2 Rudvalis.Model) : Subgroup Rudvalis.Model) ≤ _ at hh
    rwa [hg] at hh
  have hc : Nat.card W = Nat.card E := by
    rw [card_map_of_injective a.injective,card_map_of_injective Subtype.val_injective]
  rw [←hc]
  by_cases hW : W = ⊥
  · simp [hW]
  obtain ⟨i,hi⟩ := Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.elementaryCatalogue
    W hW hWP hWN inferInstance
  let : IsElementaryAbelian 2 (Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.elementary i) := hi ▸ inferInstanceAs (IsElementaryAbelian 2 W)
  rw [hi]
  exact rudvalis_candidate_card_le i

open Held Held.LocalPairs.PairCoverage Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
open Held.TwoLocalCandidates
private theorem max34_seven_free (i : Bool) : ¬ 7 ∣ Nat.card (localOvergroup i) := by
  let q := localQuotientMap i
  let f := SixPoint.quotientAction i
  have hk : ¬ 7 ∣ Nat.card f.ker := fun h =>
    (by decide : ¬ 7 ∣ 3) (h.trans (ThreeCoreBounds.quotientAction_kernel_card_dvd_three i))
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


open Held.LocalPairs.SylowGeometry.Calculations
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
private theorem held_normal_sixtyfour_seven_free (T : Sylow 2 He) (U : Subgroup He)
    (hUT : U ≤ T) [IsElementaryAbelian 2 U] (hc : Nat.card U = 64)
    (hn : (U.subgroupOf (T : Subgroup He)).Normal) :
    ¬ 7 ∣ Nat.card (normalizer (U : Set He)) := by
  have hTN := (normal_subgroupOf_iff_le_normalizer hUT).mp hn
  obtain ⟨P,hP⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq He T P
  let a := MulAut.conj g
  let W := U.map a.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hTP : (T : Subgroup He).map a.toMonoidHom = representative := by
    change ((g • T : Sylow 2 He) : Subgroup He) = representative
    rw [hg,hP]
  have hWP : W ≤ representative := hTP ▸ map_mono hUT
  have hPN : representative ≤ normalizer (W : Set He) := by
    rw [←hTP]
    exact (map_mono hTN).trans (le_normalizer_map a.toMonoidHom)
  let E := W.subgroupOf representative
  have hE : E.Normal := (normal_subgroupOf_iff_le_normalizer hWP).mpr hPN
  have hcE : Nat.card E = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hWP).toEquiv,card_map_of_injective a.injective,hc]
  have heE : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hWP
  have hrow := (Held.AutomorphismLocalPair.representative_normal_elementary_order64_iff E).mp
    ⟨hE,heE,hcE⟩
  have hgraph := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  have hident := normalizer_identities representative_isPGroup hgraph
    (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hgraph)
  have hnot : ¬ 7 ∣ Nat.card (normalizer (W : Set He)) := by
    have heW : W = E.map representative.subtype := (map_subgroupOf_eq_of_le hWP).symm
    rcases hrow with he | he
    · rw [heW,he]
      change ¬ 7 ∣ Nat.card (normalizer (ambient (distinguished 3) : Set He))
      rw [hident,card_map_of_injective (MulAut.conj _).injective]
      exact max34_seven_free true
    · rw [heW,he]
      change ¬ 7 ∣ Nat.card (normalizer (ambient (distinguished 4) : Set He))
      rw [hident,card_map_of_injective (MulAut.conj _).injective]
      exact max34_seven_free false
  rwa [show W = U.map a.toMonoidHom from rfl,←map_equiv_normalizer_eq,
    card_map_of_injective a.injective] at hnot

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The normal moving subgroup has order64, exceeding the native Rudvalis bound32. -/
theorem doubleNatural_four_adapted_component_not_rudvalis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK ⟨e⟩
  obtain ⟨P,hUP,hn,he,hcard,hi⟩ := D.doubleNatural_four_adapted_component_moving_normalSylow h B S w hw K hK
  let U := (⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf K
  let : IsElementaryAbelian 2 U := he
  have hb := NormalSylowElementary.bound_surjective (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) 32
    (NormalSylowElementary.bound_equiv e 32 Nonsingular.rudvalis_normal_elementary_bound)
    P U hUP hn hi
  rw [hcard] at hb
  omega

/-- A Held normal elementary subgroup of order64 has seven-free normalizer,
whereas the literal point residual has an L3(2) two-core quotient. -/
theorem doubleNatural_four_adapted_component_not_held
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ Nonempty ((K ⧸ center K) ≃* Held.He) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK ⟨e⟩
  obtain ⟨P,hUP,hn,he,hcard,hi⟩ := D.doubleNatural_four_adapted_component_moving_normalSylow h B S w hw K hK
  let U := (⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf K
  let : IsElementaryAbelian 2 U := he
  let q₀ := QuotientGroup.mk' (center K)
  let q := e.toMonoidHom.comp q₀
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hq
  let E := U.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hEQ : E ≤ (Q : Subgroup Held.He) := map_mono hUP
  have hnE : (E.subgroupOf (Q : Subgroup Held.He)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hEQ).mpr
    rintro _ ⟨x,hx,rfl⟩
    exact le_normalizer_map q (mem_map_of_mem q
      ((normal_subgroupOf_iff_le_normalizer hUP).mp hn hx))
  have hiq : Function.Injective (q.comp U.subtype) := e.injective.comp hi
  have hcE : Nat.card E = 64 := by
    have heq : Nat.card E = Nat.card U := Nat.card_congr
      (MulEquiv.ofBijective (q.subgroupMap U) ⟨by
        intro x y hxy
        exact hiq (congrArg Subtype.val hxy),q.subgroupMap_surjective U⟩).symm.toEquiv
    exact heq.trans hcard
  have hnot := Nonsingular.held_normal_sixtyfour_seven_free Q E hEQ hcE hnE
  let A := (B.pointResidual w).subgroupOf K
  obtain ⟨hperf,⟨eA⟩,hne,hele,hmove,hAN⟩ :=
    D.doubleNatural_adapted_component_local_marking h B S w hw K hK
  have h7 : 7 ∣ Nat.card (A.map q₀) := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (A.map q₀)))
    rw [Nat.card_congr (eA.trans Matrix.PSL3Two.equiv.symm).toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have h7q : 7 ∣ Nat.card (A.map q) := by
    rw [show A.map q = (A.map q₀).map e.toMonoidHom from (map_map _ _ _).symm,
      card_map_of_injective e.injective]
    exact h7
  have hANq : A.map q ≤ normalizer (E : Set Held.He) := by
    have hh := (map_mono (f := e.toMonoidHom) hAN).trans (le_normalizer_map e.toMonoidHom)
    simpa only [map_map] using hh
  exact hnot (h7q.trans (card_dvd_of_le hANq))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
