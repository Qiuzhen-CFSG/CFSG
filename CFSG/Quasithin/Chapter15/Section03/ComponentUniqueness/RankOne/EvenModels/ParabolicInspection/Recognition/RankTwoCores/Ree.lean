module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Transport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Parabolics

/-!
# Self-centralizing parabolic cores in the full Ree groups

For m ≥ 1, the concrete Tits system identifies the two singleton standard
parabolics with the full root-defined parabolics. Bruhat saturation puts
every proper Borel overgroup inside one of them. The existing full-parabolic
core calculations include the complementary tori; Sylow-overgroup inheritance
therefore covers every intermediate subgroup, including the Borel itself.
Conjugacy transports the conclusion to each specified Sylow subgroup.

The abstract two-generator lattice step is kept separate from the concrete
Ree quotient to avoid expanding its large matrix and normalizer instances.
No ambient order or simplicity theorem is used.

Source: Aschbacher--Smith, A.2.4, p.33, and 15.3.43, p.1140; GLS3 2.6.5.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
namespace ReeCores
open ReeF4 ReeF4.LargeLocalSeeds ReeF4.ConverseParabolics
open ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open ReeF4.SectionGeometry.BNPair
attribute [local instance] borel_inf_normalizerWords_normal

private theorem rankTwo_cover {H : Type*} [Group H]
    (T : Theory.AlgebraicGroup.TitsSystem (X := H))
    {s t : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hS : T.S = {s, t})
    (Q : Subgroup H) (hBQ : T.B ≤ Q) (hQ : Q < ⊤) :
    Q ≤ T.standardParabolic {s} ∨ Q ≤ T.standardParabolic {t} := by
  classical
  have he : Q = T.standardParabolic (T.simpleIndices Q) :=
    T.subgroup_eq_standardParabolic_simpleIndices Q hBQ
  have hnot : ¬ (s ∈ T.simpleIndices Q ∧ t ∈ T.simpleIndices Q) := by
    rintro ⟨ha, hb⟩
    have hi : T.simpleIndices Q = T.S := by
      apply Set.Subset.antisymm (T.simpleIndices_subset Q)
      rw [hS]
      intro w hw
      rcases hw with rfl | rfl <;> assumption
    rw [hi, T.standardParabolic_S] at he
    exact hQ.ne he
  by_cases hs : s ∈ T.simpleIndices Q
  · left
    rw [he]
    apply T.standardParabolic_mono
    intro w hw
    have hi := T.simpleIndices_subset Q hw
    rw [hS] at hi
    rcases hi with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hnot ⟨hs, hw⟩).elim
  · right
    rw [he]
    apply T.standardParabolic_mono
    intro w hw
    have hi := T.simpleIndices_subset Q hw
    rw [hS] at hi
    rcases hi with rfl | rfl
    · exact (hs hw).elim
    · exact Set.mem_singleton _

/-- Proper Borel overgroups are contained in one of the two full Ree parabolics. -/
theorem overgroup_le_parabolic (m : ℕ) (hm : 1 ≤ m)
    (Q : Subgroup (ReeF4.Model m)) (hBQ : ReeF4.Parabolics.borel m ≤ Q) (hQ : Q < ⊤) :
    ∃ a : Side, Q ≤ parabolic m a := by
  have hc := rankTwo_cover (titsSystem m) (simpleReflections_eq_pair m) Q hBQ hQ
  rcases hc with h | h
  · exact ⟨.linear, (standardParabolic_singleton_eq_parabolic m hm .linear) ▸ h⟩
  · exact ⟨.suzuki, (standardParabolic_singleton_eq_parabolic m hm .suzuki) ▸ h⟩

end ReeCores

/-- The full Ree carrier, at every allowed nonbinary parameter. -/
theorem ree_borelOvergroupCores (m : ℕ) (hm : 1 ≤ m) :
    BorelOvergroupCores (ReeF4.Model m) := by
  obtain ⟨T, hT⟩ := ReeF4.ConverseParabolics.exists_sylow_eq_unipotent m
  apply borelOvergroupCores_of_standard T
  intro Q hBQ hQ
  have hB : ReeF4.Parabolics.borel m ≤ Q := by
    change normalizer ((T : Subgroup (ReeF4.Model m)) : Set (ReeF4.Model m)) ≤ Q at hBQ
    rwa [hT, ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent,
      ReeF4.Parabolics.unipotent_normalizer_eq_borel] at hBQ
  obtain ⟨a, hQP⟩ := ReeCores.overgroup_le_parabolic m hm Q hB hQ
  exact core_of_sylow_overgroup_le T Q _
    ((T : Subgroup (ReeF4.Model m)).le_normalizer.trans hBQ)
    hQP (ReeF4.ConverseParabolics.parabolic_centralizer_pCore_le hm a)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
