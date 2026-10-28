module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction.Invariance
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction.Maximality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction.ModelGeometry

/-!
# Construction of the invariant Suzuki Borel

The chosen subgroup is the relative normalizer of S ∩ L₀ in the literal
orbit L₀ = ⟨L^S⟩. The two-by-three actor preserves this Sylow intersection,
so it preserves the relative normalizer. Distinct orbit components commute;
the index bound gives one or two factors, and Sylow conjugacy marks the
entire normalizer as their product Borel. Its two-core is self-centralizing,
giving F*(B) = O₂(B). Suzuki Sylow-normalizer geometry also makes B maximal
among S-invariant proper overgroups in L₀.

The construction below supplies every Borel clause needed by the local
reduction in 15.3.34. S is allowed to permute the components. The earlier
component-action assumptions (Y₊ normalizes L and the normalizer index is
at most two) remain explicit; the source assembly must supply them.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.34,
printed pp.1134--1135; the component-orbit bound is from 1.2.1(3)/A.3.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G]

/-- The literal relative normalizer supplies the containment and invariance
clauses of the Borel construction, independently of its model geometry. -/
theorem suzuki_orbit_normalizer_invariance {I L Yplus S : Subgroup G}
    (hLI : L ≤ I) (hYSI : Yplus ⊔ S ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hYL : Yplus ≤ normalizer (L : Set G)) :
    Yplus ≤ normalizer (localSpan L S : Set G) ∧
      S ⊓ localSpan L S ≤ BorelConstruction.orbitNormalizer L S ∧
      BorelConstruction.orbitNormalizer L S ≤ localSpan L S ∧
      Yplus ⊔ S ≤ normalizer (BorelConstruction.orbitNormalizer L S : Set G) := by
  obtain ⟨hspan, hnorm⟩ := BorelConstruction.orbitNormalizer_invariant hLI P hP hL m hm e
    (le_sup_left.trans hYSI) hSY hY hYL
  exact ⟨hspan, BorelConstruction.sylow_intersection_le_orbitNormalizer L S,
    BorelConstruction.orbitNormalizer_le L S, hnorm⟩

/-- Construct the invariant characteristic-two Borel in the literal component
orbit, including its whole-subgroup Suzuki marking and invariant maximality.
The component-action hypotheses do not require S to normalize L. -/
theorem exists_invariant_suzuki_orbit_borel {I L Yplus S : Subgroup G}
    (hLI : L ≤ I) (hYSI : Yplus ⊔ S ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (hYL : Yplus ≤ normalizer (L : Set G))
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2) :
    Yplus ≤ normalizer (localSpan L S : Set G) ∧
      ∃ B : Subgroup G, B ≤ localSpan L S ∧
        Yplus ⊔ S ≤ normalizer (B : Set G) ∧
        generalizedFitting B = pCore 2 B ∧
        IsSuzukiOrbitBorel (B.subgroupOf (localSpan L S)) ∧
        ∀ D : Subgroup G, B ≤ D → D ≤ localSpan L S →
          S ≤ normalizer (D : Set G) → D = B ∨ D = localSpan L S := by
  obtain ⟨hspan, _, hBL, hBN⟩ :=
    suzuki_orbit_normalizer_invariance hLI hYSI P hP hL m hm e hSY hY hYL
  refine ⟨hspan, BorelConstruction.orbitNormalizer L S, hBL, hBN, ?_, ?_, ?_⟩
  · exact BorelConstruction.orbitNormalizer_generalizedFitting hLI P hP hL m hm e hindex
  · exact BorelConstruction.orbitNormalizer_isSuzukiOrbitBorel hLI P hP hL m hm e hindex
  · exact BorelConstruction.orbitNormalizer_maximal hLI P hP hL m hm e hindex

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
