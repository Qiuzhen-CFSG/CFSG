module
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection
public import CFSG.Quasithin.Chapter3.Section02.SourceUniqueness
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow

/-!
# The original nonnormal component in Chapter 10

Construct the Fundamental Setup from the actual maximal faithful component,
then apply the proved source uniqueness theorem to its full orbit module.
Its normalizer is exactly M=N_G(L₀). The source C-component orbit bound
also shows that every nonnormal Sylow orbit consists of two factors, with
N_T(L) of index two, and the factors commute modulo O₂(⟨L,T⟩).

These results supply the opening setup of §10.1 without a chosen module,
normalization assumption or model certificate. They do not assert the seven
module alternatives of 10.1.1 or the final normalization theorem 10.0.1;
the source weak-closure and replacement arguments remain separate.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Theorem 10.0.1 and the opening of §10.1, printed p.741, using 1.2.1(2–3),
1.2.7 and 3.2.3, pp.504,506,580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem source_uniqueness
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The full original orbit module has exactly the source normalizer M. -/
theorem source_fullModule_normalizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    normalizer (D.fullModule : Set G) = D.maximalLocal := by
  have hu := D.lemma_3_2_3_uniqueness (source_uniqueness D)
  let := D.fullModule_elementary (source_uniqueness D)
  have hne : D.fullModule ≠ ⊥ := by
    intro he
    exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq he))
  exact le_antisymm (normalizer_le_of_unique_maximalTwoLocal hu.2.2
    (IsElementaryAbelian.isPGroup 2 D.fullModule) hne
    (hu.2.1.trans D.maximalLocal_normalizes_fullModule))
    D.maximalLocal_normalizes_fullModule

/-- In the nonnormal source case, the original local component has index-two
normalizer in the literal join ⟨L,T⟩. -/
theorem source_nonnormal_normalizer_index
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf (L ⊔ (T : Subgroup G)) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G))).index = 2 := by
  let H := L ⊔ (T : Subgroup G)
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk hG
    (show H ∈ Chapter1.H G from hL.2.2)
  rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hL.1 with hnormal | hi
  · apply (hn ?_).elim
    exact le_sup_right.trans
      ((normal_subgroupOf_iff_le_normalizer (show L ≤ H from le_sup_left)).mp hnormal)
  · exact hi

/-- The stabilizer T₁=N_T(L) has exactly index two in the original Sylow group. -/
theorem source_nonnormal_sylow_stabilizer_index
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2 := by
  let H := L ⊔ (T : Subgroup G)
  let N := normalizer (L.subgroupOf H : Set H)
  let S := (T : Subgroup G).subgroupOf H
  have hi : N.index = 2 := source_nonnormal_normalizer_index hG hL hn
  let : N.Normal := normal_of_index_eq_two hi
  have hd : N.relIndex S ∣ 2 := hi ▸ relIndex_dvd_index_of_normal N S
  have he : N.relIndex S = (normalizer (L : Set G)).relIndex (T : Subgroup G) := by
    dsimp only [N, S]
    rw [← subgroupOf_normalizer_eq (show L ≤ H from le_sup_left),
      relIndex_subgroupOf (show (T : Subgroup G) ≤ H from le_sup_right)]
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (hn (relIndex_eq_one.mp (he.symm.trans h1))).elim
  · exact he.symm.trans h2

/-- Every T-conjugate is one of the two original source factors, and their
join is the literal orbit L₀. -/
theorem source_nonnormal_pair
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
      localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ∀ s ∈ (T : Subgroup G),
        L.map (MulAut.conj s).toMonoidHom = L ∨
        L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  have hi := source_nonnormal_normalizer_index hG hL hn
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hn
  let tH : H := ⟨t, (show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  have hmap (s : H) :
      (A.map (MulAut.conj s).toMonoidHom).map H.subtype =
        L.map (MulAut.conj (s : G)).toMonoidHom := by
    change ((L.subgroupOf H).map (MulAut.conj s).toMonoidHom).map H.subtype = _
    rw [map_map]
    rw [show H.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : G)).toMonoidHom.comp H.subtype from rfl,
      ← map_map, map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left)]
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hm : A.map (MulAut.conj tH).toMonoidHom ≠ A := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he' := congrArg (map H.subtype) he
    rw [hmap, hmapA] at he'
    exact he'
  have hp (s : G) (hs : s ∈ (T : Subgroup G)) :
      L.map (MulAut.conj s).toMonoidHom = L ∨
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
    let sH : H := ⟨s, (show (T : Subgroup G) ≤ H from le_sup_right) hs⟩
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm sH with he | he
    · left
      change A.map (MulAut.conj sH).toMonoidHom = A at he
      have he' := congrArg (map H.subtype) he
      rw [hmap, hmapA] at he'
      exact he'
    · right
      change A.map (MulAut.conj sH).toMonoidHom = A.map (MulAut.conj tH).toMonoidHom at he
      have he' := congrArg (map H.subtype) he
      rw [hmap, hmap] at he'
      exact he'
  refine ⟨t, ht, htn, le_antisymm ?_ ?_, hp⟩
  · apply iSup_le
    intro s
    rcases hp s s.property with he | he
    · exact he.le.trans le_sup_left
    · exact he.le.trans le_sup_right
  · refine sup_le (le_componentOrbit L T) ?_
    exact le_iSup (fun s : (T : Subgroup G) =>
      L.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, ht⟩

/-- Distinct factors in the original Sylow orbit commute modulo the literal
local two-core, by the source C-component commutation theorem. -/
theorem source_conjugate_commutator_le_core
    {K : GroupClass.{u}} (hG : IsSimpleQTKE K G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf H
  let tH : H := ⟨t, (show (T : Subgroup G) ≤ H from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tH).toMonoidHom
  have hmapA : A.map H.subtype = L := map_subgroupOf_eq_of_le le_sup_left
  have hmapB : B.map H.subtype = L.map (MulAut.conj t).toMonoidHom := by
    dsimp only [B]
    rw [map_map, show H.subtype.comp (MulAut.conj tH).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp H.subtype from rfl, ← map_map, hmapA]
  have hB : B.IsCComponent := hL.1.map_equiv (MulAut.conj tH)
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map H.subtype) he).symm.trans hmapA)
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk hG
    (show H ∈ Chapter1.H G from hL.2.2)
  have hc := ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
    hQ hL.1 hB hne
  have hm := map_mono (f := H.subtype) (hc.1.trans hc.2)
  rw [map_commutator, hmapA, hmapB] at hm
  exact hm

omit [Finite G] in
/-- The orbit is strictly larger exactly in the case under treatment. -/
theorem source_lt_orbit_of_nonnormal
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) : L < localOrbit T L := by
  refine lt_of_le_of_ne (le_componentOrbit L T) ?_
  intro he
  apply hn
  rw [he]
  exact le_normalizer_componentOrbit L T

/-- The original opening reduction of Chapter 10: construct the genuine
FSU and its maximal normalizer, without an assumed module or pair geometry. -/
theorem source_nonnormal_preparation
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      IsMaximalTwoLocal D.maximalLocal ∧
      normalizer (D.fullModule : Set G) = D.maximalLocal ∧
      IsElementaryAbelian 2 D.fullModule ∧
      L < localOrbit T L ∧
      (normalizer (L : Set G)).relIndex (T : Subgroup G) = 2 ∧
      ∃ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) ∧
        localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
        ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ ≤
          (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨D⟩ := source_exists_fundamentalSetup hG T L hL hf hq
  obtain ⟨t, ht, htn, he, _⟩ := source_nonnormal_pair hG hL.1 hn
  refine ⟨D, (D.lemma_3_2_3_uniqueness (source_uniqueness D)).1,
    source_fullModule_normalizer D, D.fullModule_elementary (source_uniqueness D),
    source_lt_orbit_of_nonnormal hn,
    source_nonnormal_sylow_stabilizer_index hG hL.1 hn,
    t, ht, htn, he, source_conjugate_commutator_le_core hG hL.1 ht htn⟩

end CFSG.Quasithin.Chapter10
