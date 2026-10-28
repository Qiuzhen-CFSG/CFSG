module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointResidual
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.ComponentIntersection
public import Theory.Alternating.Aut
public import Theory.GroupTheory.SimpleSubgroupSmallIndex

/-!
# Alternating and binary-linear point-component branches

The rank-two cubic argument puts the literal Y inside a point component
whose two-core quotient is A₇ or A₈. The already constructed intersection
M₁* ∩ K₁* then has Sylow index 63. In either simple quotient its index
is five, contradicting the faithful coset action and its order bound 5!.
The smaller alternating rows A₅ and A₆ have order prime to seven, whereas
the original L₁ section forces seven to divide the component quotient.

This excludes the entire alternating part of the quasisimple catalogue
and the binary-linear degree-four row. Degree five supplies the full
large source alternative, including Y ≤ K₁, through PointResidual.
PointCore.PointModels applies the resulting binary-linear branch to the
original point-core conclusion. The other quasisimple catalogue rows,
normalizer containments and escape remain with qt-d-1251-local; final
exterior assembly remains with qt-d-1251-source.

Source: Aschbacher--Smith, 12.5.3, printed pp.817--818, and A.3.18,
printed pp.51--52. The index argument replaces the corresponding inspection
of Sylow overgroups, retaining the original two-block quotient of M₁.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02

private theorem no_small_index {A : Type*} [Group A] [Finite A] [IsSimpleGroup A]
    (J : Subgroup A) (hj : J.index = 5) (hc : 120 < Nat.card A) : False := by
  have hn : J.normalCore = ⊥ := by
    rcases (inferInstance : J.normalCore.Normal).eq_bot_or_eq_top with he | he
    · exact he
    · have ht : J = ⊤ := top_unique (he ▸ J.normalCore_le)
      simp [ht] at hj
  let f := MulAction.toPermHom A (A ⧸ J)
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    (J.normalCore_eq_ker.symm.trans hn)
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_perm, ← J.index_eq_card, hj] at hb
  norm_num at hb
  omega

private theorem no_sixtyThree_index {A : Type*} [Group A] [Finite A] [IsSimpleGroup A]
    (hc : Nat.card A = 2520 ∨ Nat.card A = 20160)
    (S : Sylow 2 A) (J : Subgroup A) (hSJ : (S : Subgroup A) ≤ J)
    (hj : (S : Subgroup A).relIndex J = 63) : False := by
  have hs : (S : Subgroup A).index = 315 := by
    have hh := (S : Subgroup A).index_mul_card
    rw [S.card_eq_multiplicity] at hh
    rcases hc with hc | hc
    · rw [hc,show (Nat.factorization 2520) 2 = 3 from by decide +kernel] at hh
      omega
    · rw [hc,show (Nat.factorization 20160) 2 = 6 from by decide +kernel] at hh
      omega
  have hm := relIndex_mul_index hSJ
  rw [hj,hs] at hm
  apply no_small_index J (by omega)
  rcases hc with hc | hc <;> omega

private theorem alternating_outer_two {n : ℕ} (hn : n = 7 ∨ n = 8) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let A := alternatingGroup (Fin n)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨t,rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
    (by omega) (by omega)).surjective a
  exact ⟨QuotientGroup.mk' A t,rfl⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private theorem Y_le_point_component_of_small_alternating
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {n : ℕ} (hn : n = 7 ∨ n = 8)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n)) : s.Y ≤ K := by
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  let a := subgroupOfEquivOfLe hK.1
  let b := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : b x ∈ center (alternatingGroup (Fin n)) := (centerCongr b ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp; omega),mem_bot] at hh
    exact b.map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by
    rw [primeRank_congr 3 b]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by omega)
  have ho : IsPGroup 2 (MulAut.Outer (C ⧸ pCore 2 C)) :=
    (alternating_outer_two hn).of_equiv (MulAut.outerCongr b).symm
  let : C.Normal := hN
  have hi : Nat.Coprime 3 C.index := by
    apply cComponent_index_coprime_three_of_quotient C hK.2 hz hr
      ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))).stronglyQuasithin
        3 (by decide) (by decide))
    obtain ⟨k,hk⟩ := ho.exists_card_dvd_pow
    exact ((show Nat.Coprime 3 2 by decide).pow_right k).coprime_dvd_right hk
  have hc : primeToResidual 3 H ≤ C := primeToResidual_le C hi
  rw [s.Y_eq_primeToThree]
  exact (embedded_primeToResidual_mono 3 (s.P_le_M₁.trans inf_le_right)).trans
    ((map_mono (f := H.subtype) hc).trans_eq (map_subgroupOf_eq_of_le hK.1))

/-- The actual point component cannot have two-core quotient A₇ or A₈. -/
theorem point_component_not_small_alternating
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {n : ℕ} (hn : n = 7 ∨ n = 8) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  have hY := s.Y_le_point_component_of_small_alternating h hK hN hn e
  let a := subgroupOfEquivOfLe hK.1
  let b : (K ⧸ pCore 2 K) ≃* s.pointCoreImage K :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
      (cComponentTwoCoreQuotientEquiv hK.2)
  let c := b.symm.trans e
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simp; omega)
  let : IsSimpleGroup (s.pointCoreImage K) := c.isSimpleGroup
  have hc : Nat.card (s.pointCoreImage K) = 2520 ∨
      Nat.card (s.pointCoreImage K) = 20160 := by
    rw [Nat.card_congr c.toEquiv,nat_card_alternatingGroup]
    rcases hn with rfl | rfl <;> norm_num [Nat.factorial]
  obtain ⟨S,hSJ,hi⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  exact no_sixtyThree_index hc S (s.pointComponentParabolic K) hSJ hi

/-- The binary degree-four point row is the excluded actual A₈ model. -/
theorem point_component_not_linear_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
  exact s.point_component_not_small_alternating h hK hLK hN (.inr rfl)
    ⟨(e.trans (Atlas.fieldEquivPSL 4 (FiniteField.ringEquivOfCardEq hc))).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩

private theorem seven_dvd_point_component_quotient {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) : 7 ∣ Nat.card (K ⧸ pCore 2 K) := by
  have hB : 7 ∣ Nat.card (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1)) := by
    rw [Nat.card_congr (s.marking.LiCoreEquiv 1 (.inl rfl)).toEquiv]
    change 7 ∣ Nat.card SL(3,ZMod 2)
    rw [Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  have h7 : 7 ∣ Nat.card K := (hB.trans
    (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (s.marking.Li 1)))
      (QuotientGroup.mk'_surjective _))).trans (card_dvd_of_le hLK)
  have hc : Nat.Coprime 7 (Nat.card (pCore 2 K)) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_dvd_pow
    exact ((show Nat.Coprime 7 2 by decide).pow_right k).coprime_dvd_right hk
  have he := (pCore 2 K).card_mul_index
  rw [index_eq_card] at he
  rw [←he] at h7
  exact hc.dvd_of_dvd_mul_left h7

/-- The full alternating branch of the source point-component sieve is impossible. -/
theorem point_component_not_alternating
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  by_cases hs : n = 7 ∨ n = 8
  · exact s.point_component_not_small_alternating h hK hLK hN hs ⟨e⟩
  have h7 := s.seven_dvd_point_component_quotient hLK
  have hn' : n = 5 ∨ n = 6 := by omega
  rcases hn' with rfl | rfl
  all_goals rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at h7
  all_goals norm_num [Nat.factorial] at h7

/-- In the binary higher-linear branch, the quotient is L₅(2) and the literal Y lies in K₁. -/
theorem local_point_component_alternative_of_binary_linear
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    LocalComponentAlternative s 1 K := by
  rcases hn with rfl | rfl
  · exact (s.point_component_not_linear_four h hK hLK hN hm).elim
  · exact s.local_point_component_large_alternative h hK hN (.inl hm)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
