module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.Components
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairSource
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The seed alternatives forced by Cartan escape

The generating seed from E.2.2 has the original two-residual as its full
Sylow orbit. Source 1.2.7 controls that orbit whenever the seed is maximal.
Source 1.2.8(3) makes every moved non-PSL2(4) seed maximal, so local Cartan
escape leaves only an unmoved seed or a moved seed with PSL2(4) quotient.
The latter conclusion concerns the seed, not the quotient of the whole orbit.

Source: Aschbacher--Smith, 1.2.7--8 and 5.1.10--12, pp.506--507,634--635.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- Maximality controls the entire Sylow orbit, including a moved seed. -/
theorem overgroup_normalizes_seed_orbit {T : Sylow 2 G} {K H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G))
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    Y ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G) := by
  have hcore : pCore 2 Y ≠ ⊥ := by
    intro he
    apply hY.1
    change (pCore 2 Y).map Y.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨M, hM, hYM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot Y hcore
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hK
  have he := hu.normalizer_unique M hM (hgen.le.trans (hY.2.trans hYM))
  exact he ▸ hYM

/-- The original escaping branch cannot have a moved non-A5 seed. -/
theorem moved_seed_linear_four_of_escape
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hgen : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hmoved : K ≠ residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 := by
  by_contra hnot
  have hm : K < conjugateSpanBy K (T : Subgroup G) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    change K < componentOrbit K (T : Subgroup G)
    exact lt_of_le_of_ne (le_componentOrbit K _) (fun he => hmoved (he.trans horbit))
  have hmax := Chapter1.Section02.MovedMaximality.moved_local_mem_LStar hG T hK hm hnot
  have hn := overgroup_normalizes_seed_orbit hG hmax hgen hY
  rw [horbit] at hn
  exact hescape (inf_le_right.trans hn)

/-- E.2.2 supplies a real seed. Escape leaves either the whole residual or
the paired case with a PSL2(4) seed; no quotient of the whole pair is asserted. -/
theorem exists_escape_seed {T : Sylow 2 G} {M H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      (K = residual H ∨
        (K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)) := by
  obtain ⟨K, hKH, hK, hq, hg, hl, ho⟩ := exists_seed hG hTM hH hgen
  refine ⟨K, hKH, hK, hq, hg, hl, ho, ?_⟩
  by_cases he : K = residual H
  · exact Or.inl he
  · exact Or.inr ⟨lt_of_le_of_ne ((le_componentOrbit K _).trans_eq ho) he,
      moved_seed_linear_four_of_escape hG hl hg ho he hY hescape⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
