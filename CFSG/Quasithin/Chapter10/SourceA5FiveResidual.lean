module
public import CFSG.Quasithin.Chapter10.SourceCubicResidual
public import Theory.GroupTheory.TwoOrbitOddPrime.Residual
public import Theory.Alternating.Aut

/-!
# The five-residual in the original nonnormal A₅ configuration

The actual maximal normalizer M contains L as a nonnormal C-component with
two conjugates. Both A₅ factors have order divisible by five, while their
outer groups are two-groups. The ambient five-rank bound therefore makes
their orbit product L₀ the prime-to-five residual of M.

The theorem retains the original Fundamental Setup and its literal subgroup
embeddings. Together with the cubic residual it removes the odd part of the
multiplicity centralizer in the minimal-module replacement argument.
Source: Aschbacher--Smith 10.1.3 and D.3.21, printed pp.741 and 206.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))

private theorem alternatingFive_outer_two :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin 5))) := by
  let A := alternatingGroup (Fin 5)
  have htwo : IsPGroup 2 (Equiv.Perm (Fin 5) ⧸ A) := by
    apply IsPGroup.of_card (n := 1)
    rw [←A.index_eq_card,alternatingGroup.index_eq_two]
    rfl
  apply htwo.of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A σ,rfl⟩

include D e

/-- The original A₅ orbit is O^{5′}(M), with no additional local hypothesis. -/
theorem source_nonnormal_a5_five_residual
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (primeToResidual 5 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L := by
  let M := D.maximalLocal
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hlocal : IsSQTK KnownSimple.IsKnownSimple M :=
    D.simpleQTKE.twoLocal_sqtk hu.normalizer_maximal.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  have hnot : ¬ A.Normal := by
    intro ha
    exact hn (hTM.trans ((normal_subgroupOf_iff_le_normalizer hLM).mp ha))
  obtain ⟨hi,_⟩ := (Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ
    D.component_in_maximalLocal).resolve_left hnot
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM)
      (pCore_map_iso 2 _)).trans e
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_mulEquiv ((QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM)
      (pCore_map_iso 2 _)).symm)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eA.isSimpleGroup
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr eA ⟨z,hz⟩).property
    change eA z ∈ center (alternatingGroup (Fin 5)) at he
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact eA.map_eq_one_iff.mp he
  have hdA : 5 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hoA : Nat.Coprime 5 (Nat.card (MulAut.Outer (A ⧸ pCore 2 A))) := by
    rw [Nat.card_congr (MulAut.outerCongr eA).toEquiv]
    obtain ⟨n,hn⟩ := alternatingFive_outer_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 5 2).pow_right n).coprime_dvd_right hn
  have hr := TwoOrbitOddPrime.nonnormal_component_primeToResidual 5 (by decide)
    D.component_in_maximalLocal hi hz hdA
    (hlocal.stronglyQuasithin 5 (by decide) (by decide)) hoA
  rw [hr,map_conjugateSpanBy,map_subgroupOf_eq_of_le hLM]
  have htop : (⊤ : Subgroup M).map M.subtype = M := by
    ext g
    exact ⟨fun ⟨m,_,he⟩ => he ▸ m.property,fun hg => ⟨⟨g,hg⟩,mem_top _,rfl⟩⟩
  rw [htop]
  apply le_antisymm (conjugateSpanBy_le (le_componentOrbit L T) le_rfl)
  change (⨆ t : (T : Subgroup G), L.map (MulAut.conj (t : G)).toMonoidHom) ≤ _
  apply iSup_le
  intro t x hx
  obtain ⟨l,hl,rfl⟩ := hx
  exact subset_closure ⟨t,hTM t.property,l,hl,rfl⟩

/-- The source five-prime index used by the actual multiplicity action. -/
theorem source_nonnormal_a5_orbit_index_coprime_five
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nat.Coprime 5 ((localOrbit T L).subgroupOf D.maximalLocal).index := by
  have he : (localOrbit T L).subgroupOf D.maximalLocal = primeToResidual 5 D.maximalLocal := by
    apply map_injective D.maximalLocal.subtype_injective
    rw [map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer,
      source_nonnormal_a5_five_residual D e hn]
  rw [he]
  exact primeToResidual_index_coprime 5

end CFSG.Quasithin.Chapter10
