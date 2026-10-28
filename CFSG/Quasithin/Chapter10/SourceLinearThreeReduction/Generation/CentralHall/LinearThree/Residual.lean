module
public import CFSG.Quasithin.Chapter10.SourceCubicResidual
public import Theory.GroupTheory.TwoOrbitOddPrime.Residual
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# The seven-residual of the original linear-three orbit

The two actual SL₃(2) component quotients exhaust the ambient seven-rank.
Their outer automorphism groups have order two. The odd-prime orbit theorem
therefore identifies the literal orbit L₀ with O^{7′}(M), giving the missing
prime-to-seven index used to place the faithful Hall actor inside L₀.

Source: Aschbacher--Smith, 10.1.3 and 10.2.3, printed pp.742 and745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
private local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)

include D e

/-- The original linear-three orbit is O^{7′}(M), with no additional local hypothesis. -/
theorem source_linearThree_seven_residual
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (primeToResidual 7 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L := by
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
  let eA : (A ⧸ pCore 2 A) ≃* Matrix.PSL3Two.SL :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM)
      (pCore_map_iso 2 _)).trans e
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_mulEquiv ((QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM)
      (pCore_map_iso 2 _)).symm)
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eA.isSimpleGroup
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr eA ⟨z,hz⟩).property
    change eA z ∈ center (Matrix.PSL3Two.SL) at he
    rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at he
    exact eA.map_eq_one_iff.mp he
  have hdA : 7 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eA.toEquiv,Matrix.PSL3Two.card_SL]
    norm_num
  have hoA : Nat.Coprime 7 (Nat.card (MulAut.Outer (A ⧸ pCore 2 A))) := by
    rw [Nat.card_congr (MulAut.outerCongr eA).toEquiv]
    obtain ⟨n,hn⟩ := Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 7 2).pow_right n).coprime_dvd_right hn
  have hr := TwoOrbitOddPrime.nonnormal_component_primeToResidual 7 (by decide)
    D.component_in_maximalLocal hi hz hdA
    (hlocal.stronglyQuasithin 7 (by decide) (by decide)) hoA
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

/-- The source seven-prime index used by the actual multiplicity action. -/
theorem source_linearThree_orbit_index_coprime_seven
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nat.Coprime 7 ((localOrbit T L).subgroupOf D.maximalLocal).index := by
  have he : (localOrbit T L).subgroupOf D.maximalLocal = primeToResidual 7 D.maximalLocal := by
    apply map_injective D.maximalLocal.subtype_injective
    rw [map_subgroupOf_eq_of_le (localOrbit T L).le_normalizer,
      source_linearThree_seven_residual D e hn]
  rw [he]
  exact primeToResidual_index_coprime 7

end CFSG.Quasithin.Chapter10
