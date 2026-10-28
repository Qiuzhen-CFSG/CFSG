module

public import Theory.AlgebraicGroup.BNPair.MaximalParabolic
public import Theory.GroupTheory.CoreFreeFromLocal
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData

/-!
# Core-free maximal Ree parabolics: geometric reduction

The parabolics here are the fixed intersections of the actual root-generated
split parabolics with the concrete exceptional fixed group `Model m`.
An identification with a maximal standard parabolic in a Tits system proves
maximality. Normality and self-centralization of its root radical, together
with disjointness from an opposite parabolic, prove triviality of its normal
core without using simplicity of `Model m`.

The concrete Tits-system identification, radical centralizer calculation, and
opposition calculation remain explicit inputs. These conditional theorems do
not yet establish the unconditional core-free witness for every `m ≥ 1`.

Sources: GLS3, Theorems 2.3.4–5 and 2.6.5, Definition 2.6.6, and Section 3.2,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/

public section

namespace ReeF4.SectionGeometry

open Theory.AlgebraicGroup Subgroup LargeLocalSeeds Parabolics

/-- The local radical calculation and opposition suffice for trivial core.
The normalizer and centralizer conditions are relative to the full parabolic. -/
theorem parabolic_normalCore_eq_bot_of_radical
    (m : ℕ) (side : Side)
    (hnorm : parabolic m side ≤ normalizer (radical m side : Set (Model m)))
    (hc : centralizer ((radical m side).subgroupOf (parabolic m side) :
      Set (parabolic m side)) ≤ (radical m side).subgroupOf (parabolic m side))
    (hop : ∃ g : Model m, Disjoint (radical m side)
      ((parabolic m side).comap (MulAut.conj g).toMonoidHom)) :
    (parabolic m side).normalCore = ⊥ := by
  have hRP : radical m side ≤ parabolic m side :=
    (radical_le_unipotent m side).trans
      ((unipotent_le_borel m).trans (borel_le_parabolic m side))
  let : ((radical m side).subgroupOf (parabolic m side)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRP).mpr hnorm
  obtain ⟨g, hg⟩ := hop
  apply normalCore_eq_bot_of_disjoint_conjugate (parabolic m side)
    ((radical m side).subgroupOf (parabolic m side)) hc g
  rwa [map_subgroupOf_eq_of_le hRP]

/-- Conditional assembly at the exact root-defined parabolic. The BN-pair
identification gives maximality; the radical and opposition give trivial core.
Every geometric premise must still be constructed for the concrete Ree model. -/
theorem exists_coreFree_coatom_of_geometry
    (m : ℕ) (side : Side) (T : TitsSystem (X := Model m))
    (s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (hs : s ∈ T.S)
    (hP : T.standardParabolic (T.S \ {s}) = parabolic m side)
    (hnorm : parabolic m side ≤ normalizer (radical m side : Set (Model m)))
    (hc : centralizer ((radical m side).subgroupOf (parabolic m side) :
      Set (parabolic m side)) ≤ (radical m side).subgroupOf (parabolic m side))
    (hop : ∃ g : Model m, Disjoint (radical m side)
      ((parabolic m side).comap (MulAut.conj g).toMonoidHom)) :
    ∃ P : Subgroup (Model m), IsCoatom P ∧ P.normalCore = ⊥ := by
  refine ⟨parabolic m side, ?_, parabolic_normalCore_eq_bot_of_radical m side hnorm hc hop⟩
  rw [← hP]
  exact T.standardParabolic_isCoatom hs

end ReeF4.SectionGeometry
