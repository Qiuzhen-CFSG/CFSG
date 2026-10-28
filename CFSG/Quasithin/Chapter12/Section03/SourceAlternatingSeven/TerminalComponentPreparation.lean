module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalInterfaces
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality

/-!
# The point-centralizer embedding in 12.3.12

The escaping residual is normalized by the original Sylow subgroup. Once
12.2.7 supplies membership in the local component family, genuine 1.2.4
embeds it in a normal C-component of the actual point centralizer. That
component extends to a maximal local component in G. In particular,
maximality of the original residual already implies its relative normality.

The selected H-star also proves the multiple-overgroup standing guard.
Thus an outside H-star for a second maximal residual is constructed from
the original inputs; no additional Chapter 13 assumption is needed.
Source: Aschbacher--Smith, 12.3.12, printed p.811; 1.2.4 and 1.2.7,
printed pp.505--506.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The original H is the join of its two-residual and its Sylow subgroup. -/
theorem residual_sup_sylow : P.K ⊔ (T : Subgroup G) = P.H := by
  have hTH : (T : Subgroup G) ≤ P.H := P.minimal.1.1.2
  have he := congrArg (map P.H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at he
  exact he

/-- Residual normalization is intrinsic to H, then transported to G. -/
theorem sylow_normalizes_residual : (T : Subgroup G) ≤ normalizer (P.K : Set G) :=
  P.minimal.1.1.2.trans (P.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P.H (pResidual 2 P.H)))

theorem residual_le_pointCentralizer : P.K ≤ P.pointCentralizer :=
  (map_subtype_le _).trans P.centralizes

theorem sylow_le_pointCentralizer : (T : Subgroup G) ≤ P.pointCentralizer :=
  P.minimal.1.1.2.trans P.centralizes

theorem point_order : orderOf (P.point : G) = 2 := by
  apply orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp P.central).2.2
  intro he
  exact P.nonidentity (Subtype.ext he)

theorem pointCentralizer_mem_HOver :
    P.pointCentralizer ∈ Chapter1.HOver G (T : Set G) :=
  ⟨Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer P.point_order),
    P.sylow_le_pointCentralizer⟩

theorem pointCentralizer_sqtk :
    IsSQTK KnownSimple.IsKnownSimple P.pointCentralizer :=
  S.hypothesis.simpleQTKE.involution_centralizer_sqtk P.point_order

/-- The rank hypothesis needed by 1.2.4 descends through this two-core. -/
theorem pointCentralizer_quotient_sqtk :
    IsSQTK KnownSimple.IsKnownSimple
      (P.pointCentralizer ⧸ pCore 2 P.pointCentralizer) := by
  refine ⟨?_, P.pointCentralizer_sqtk.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (P.pointCentralizer_sqtk.stronglyQuasithin p hp ho)

/-- Escape forces actual movement of the original omega-center. -/
theorem omega_commutator_ne_bot
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ⁅P.Z, P.K⁆ ≠ ⊥ := by
  intro he
  apply P.residual_escape structural
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
    (omega_center_centralizer_le S D structural)

/-- The point-centralizer component and a maximal local component above it.
All normality remains relative to the literal point centralizer. -/
structure Overcomponents where
  E : Subgroup G
  Y : Subgroup G
  residual_le : P.K ≤ E
  component : E ∈ Chapter1.cComponentsIn P.pointCentralizer
  normalizes : P.pointCentralizer ≤ normalizer (E : Set G)
  local_mem : E ∈ Chapter1.L G (T : Subgroup G)
  le_maximal : E ≤ Y
  maximal : Y ∈ Chapter1.LStar G (T : Subgroup G)

/-- Original 1.2.4 constructs the containing component once 12.2.7 supplies
local-family membership of the nonsolvable residual. -/
theorem overcomponents_nonempty (hlocal : P.K ∈ Chapter1.L G (T : Subgroup G)) :
    Nonempty P.Overcomponents := by
  let C := P.pointCentralizer
  let TC := T.subtype P.sylow_le_pointCentralizer
  have hKC : P.K.subgroupOf C ∈ Chapter1.L C (TC : Subgroup C) :=
    (Chapter1.mem_LIn_iff_subgroupOf P.sylow_le_pointCentralizer
      P.residual_le_pointCentralizer).mp ⟨P.residual_le_pointCentralizer, hlocal⟩
  have hn : (TC : Subgroup C) ≤ normalizer (P.K.subgroupOf C : Set C) := by
    intro t ht
    apply mem_normalizer_iff.mpr
    intro k
    change ((k : G) ∈ P.K ↔ (t : G) * (k : G) * (t : G)⁻¹ ∈ P.K)
    exact mem_normalizer_iff.mp (P.sylow_normalizes_residual ht) k
  obtain ⟨E, ⟨hE, hKE, hnE⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      P.pointCentralizer_quotient_sqtk TC hKC hn
  let E' := E.map C.subtype
  have hE'C : E' ≤ C := map_subtype_le _
  have hE'sub : E'.subgroupOf C = E :=
    comap_map_eq_self_of_injective C.subtype_injective E
  have hc : E' ∈ Chapter1.cComponentsIn C := ⟨hE'C, hE'sub.symm ▸ hE⟩
  have hElocal := (Chapter1.lemma_1_2_6 T P.pointCentralizer_mem_HOver).1 hc
  obtain ⟨Y, hY, hEY⟩ := Chapter1.exists_mem_LStar_ge hElocal.2
  refine ⟨⟨E', Y, ?_, hc, ?_, hElocal.2, hEY, hY⟩⟩
  · calc
      P.K = (P.K.subgroupOf C).map C.subtype :=
        (map_subgroupOf_eq_of_le P.residual_le_pointCentralizer).symm
      _ ≤ E' := map_mono hKE
  · exact (normal_subgroupOf_iff_le_normalizer hE'C).mp (hE'sub.symm ▸ hnE)

/-- Maximality of K eliminates both containments and gives normality in G_e. -/
theorem pointCentralizer_normalizes_of_maximal
    (hmax : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    P.pointCentralizer ≤ normalizer (P.K : Set G) := by
  obtain ⟨F⟩ := P.overcomponents_nonempty hmax.1
  exact hmax.2 F.E F.local_mem F.residual_le ▸ F.normalizes

include P in
/-- The original escaping H supplies an actual maximal two-local outside M. -/
theorem exists_outside_maximal :
    ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ (T : Subgroup G) ≤ N ∧
      ¬ N ≤ normalizer (L : Set G) := by
  have hcore : pCore 2 P.H ≠ ⊥ := by
    intro he
    apply P.minimal.1.1.1
    change (pCore 2 P.H).map P.H.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨N, hN, hHN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot P.H hcore
  exact ⟨N, hN, P.minimal.1.1.2.trans hHN, fun hn => P.minimal.1.2 (hHN.trans hn)⟩

include P in
/-- No new global guard is required for the second H-star in 12.3.12. -/
theorem many_maximal_overgroups :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.hypothesis.simpleQTKE T S.hypothesis.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    have he : componentOrbit L (T : Subgroup G) = L :=
      S.chosen.localOrbit_eq
    simpa only [he] using hu.normalizer_maximal
  obtain ⟨N, hN, hTN, hn⟩ := P.exists_outside_maximal
  apply Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
  exact ⟨⟨N, ⟨hN, hTN⟩, normalizer (L : Set G),
    ⟨hm, S.chosen.sylow_normalizes_component⟩, fun he => hn he.le⟩, Set.toFinite _⟩

/-- The maximal-residual branch has an actual comparison H-star which moves Z. -/
theorem exists_moving_hstar_of_maximal
    (hmax : P.K ∈ Chapter1.LStar G (T : Subgroup G)) :
    ∃ H₁ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (P.K : Set G)),
      ¬ H₁ ≤ P.pointCentralizer ∧ ⁅P.Z, H₁⁆ ≠ ⊥ := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.hypothesis.simpleQTKE T hmax
  have horbit : componentOrbit P.K (T : Subgroup G) = P.K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      P.sylow_normalizes_residual) (le_componentOrbit _ _)
  have hm : IsMaximalTwoLocal (normalizer (P.K : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  obtain ⟨H₁, hH₁⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T P.many_maximal_overgroups _ hm
      P.sylow_normalizes_residual)
  have hn : ¬ H₁ ≤ P.pointCentralizer :=
    fun hh => hH₁.1.2 (hh.trans (P.pointCentralizer_normalizes_of_maximal hmax))
  refine ⟨H₁, hH₁, hn, ?_⟩
  intro he
  exact hn ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans
    (centralizer_le (Set.singleton_subset_iff.mpr P.central)))

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
