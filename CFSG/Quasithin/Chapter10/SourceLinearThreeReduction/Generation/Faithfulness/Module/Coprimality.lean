module
public import CFSG.Quasithin.Chapter10.SourceNonnormalFixedResidual
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.SpecificGroups.Janko1.Model.Certification
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.TwoOrbitOddPrime.SectionCentralizer
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Inputs

/-!
# Coprimality for the original nonnormal Hall kernel

The two conjugate component quotients are centerless. For each odd prime
in their order, their commuting images exhaust the local prime-rank bound.
Consequently the literal centralizer of L₀/O₂(L₀) has order prime to that
prime. Every odd subgroup of this section centralizer, and in particular
the original Hall kernel, has order coprime to |L/O₂(L)|.

This proves the coprimality needed in the FF branch of 10.2.3(2) without
requiring the full residual assertion of 10.1.3. Module fixation and the
4.4.3 normalizer application remain separate obligations owned by the
Hall-faithfulness assembly. The quotient, local subgroup and Hall maps
throughout are the original ones.

Source: Aschbacher--Smith, 1.2.1--2 and the opening proof of 10.2.3(2),
printed pp.503--504,745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter1.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

private theorem simple_perfect_center {Q : Type*} [Group Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim

private theorem model_center {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] (hm : NonnormalCComponentModel Q) : center Q = ⊥ := by
  have hlinear {q : ℕ} (h : ClassicalGroup.IsPSL Q 2 q) : center Q = ⊥ := by
    obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
    exact center_transport e.symm (GorensteinWalter.psl2_center_eq_bot F)
  cases hm with
  | linear_even n hn he => exact hlinear he
  | linear_prime p hp ho he => exact hlinear he
  | suzuki m hm he =>
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    let : IsSimpleGroup Q := he.some.isSimpleGroup
    exact simple_perfect_center
  | janko he =>
    let : IsSimpleGroup Q := he.some.isSimpleGroup
    exact simple_perfect_center

private theorem source_local_sqtk (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1

/-- The actual component quotient in a nonnormal fundamental setup is centerless. -/
theorem source_nonnormal_component_core_center
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hlocal := source_local_sqtk D
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := fun ha =>
    hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨_,hm⟩ := (proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let e : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM) (pCore_map_iso 2 _)
  let := D.quasisimple
  exact model_center (hm.of_mulEquiv e.symm)

/-- An odd prime dividing the component quotient cannot divide the literal section centralizer. -/
theorem source_nonnormal_sectionCentralizer_prime_coprime
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hd : p ∣ Nat.card (L ⧸ pCore 2 L)) :
    Nat.Coprime p (Nat.card (sectionCentralizer (localOrbit T L))) := by
  let M := D.maximalLocal
  let X := localOrbit T L
  let A := L.subgroupOf M
  let C := sectionCentralizer X
  have hCM : C ≤ M := ((le_sectionCentralizer_iff C X).mp le_rfl).1
  have hLM : L ≤ M := (le_componentOrbit L T).trans X.le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tM : M := ⟨t,hTM ht⟩
  have htnM : tM ∉ normalizer (A : Set M) := by
    rw [←subgroupOf_normalizer_eq hLM]
    exact htn
  let e : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM) (pCore_map_iso 2 _)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (A ⧸ pCore 2 A) = ⊥ :=
    center_transport e.symm (source_nonnormal_component_core_center D hn)
  have hdA : p ∣ Nat.card (A ⧸ pCore 2 A) := by rwa [Nat.card_congr e.toEquiv]
  have hmap : (A ⊔ A.conjBy tM).map M.subtype = X := by
    rw [Subgroup.map_sup]
    change A.map M.subtype ⊔ (A.map (MulAut.conj tM).toMonoidHom).map M.subtype = X
    rw [map_map,show M.subtype.comp (MulAut.conj tM).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le hLM,←hpair]
  have hc : ⁅C.subgroupOf M,A ⊔ A.conjBy tM⁆ ≤ pCore 2 M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hCM,hmap]
    exact (((le_sectionCentralizer_iff C X).mp le_rfl).2).trans
      (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl)
  have hh := TwoOrbitOddPrime.cComponent_pair_sectionKernel_coprime p hp
    D.component_in_maximalLocal hz tM htnM hdA
    ((source_local_sqtk D).stronglyQuasithin p Fact.out
      ((Fact.out : p.Prime).odd_of_ne_two hp)) (C.subgroupOf M) hc
  rwa [Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv] at hh

/-- Every odd subgroup acting trivially on the original orbit quotient has order coprime to the component quotient. -/
theorem source_nonnormal_odd_sectionKernel_coprime
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hodd : Odd (Nat.card B))
    (hB : B ≤ sectionCentralizer (localOrbit T L)) :
    Nat.Coprime (Nat.card B) (Nat.card (L ⧸ pCore 2 L)) := by
  apply Nat.coprime_of_dvd
  intro p hp hpB hpL
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpB)
  exact hp.coprime_iff_not_dvd.mp
    (source_nonnormal_sectionCentralizer_prime_coprime D hn p hp2 hpL)
    (hpB.trans (card_dvd_of_le hB))

/-- The original odd Hall kernel satisfies the coprimality used in the FF branch of 10.2.3(2). -/
theorem source_nonnormal_hall_kernel_coprime
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    Nat.Coprime (Nat.card (B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) : Subgroup G))
      (Nat.card (L ⧸ pCore 2 L)) := by
  have hodd : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact OddHall.odd_hall_odd hB
  apply source_nonnormal_odd_sectionKernel_coprime D hn _ _ inf_le_right
  apply (show Odd (Nat.card (B.map H.subtype)) by
    rwa [card_map_of_injective H.subtype_injective]).of_dvd_nat
  exact card_dvd_of_le inf_le_left
end CFSG.Quasithin.Chapter10
