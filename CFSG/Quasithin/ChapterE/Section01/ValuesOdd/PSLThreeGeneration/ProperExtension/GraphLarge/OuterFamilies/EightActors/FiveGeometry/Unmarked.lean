module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Independent prime-five model and actor-geometry contracts

The finite-family calculation only needs to detect whether the actual
quotient actor lies outside the derived subgroup. A separate identification
of that quotient with S₅ converts this to the alternating-group condition.
Consequently the matrix quotient and family-fusion calculations can proceed
independently. Their results are consumed by `familyEscapes_of_five_geometry`;
neither existence result is asserted here.

Source: Aschbacher--Smith E.1.14(7), p.214, using E.1.8 and E.1.10,
pp.210--213. The derived subgroup of S₅ is its alternating subgroup.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OddPrimeGraphExtension
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
variable (F : Type*) [Field F] [Finite F]

/-- The finite actor calculation uses the intrinsic derived subgroup,
without depending on a chosen permutation-model equivalence. -/
@[expose] def UnmarkedFiveGeometryAt (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) (z : graphExtension F) : Prop :=
  (∃ H : Subgroup (graphExtension F), (T : Subgroup _) ≤ H ∧ Group.IsSolvable H ∧
    H ⊔ normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) = ⊤) ∨
  (let K := PSUThreeGeneration.centralizerResidualOvergroup T z
   let q := QuotientGroup.mk' (solvableRadical K)
   ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧ Nat.card ((B.subgroupOf K).map q) = 4 ∧
     ¬ (B.subgroupOf K).map q ≤ _root_.commutator (K ⧸ solvableRadical K))

omit [Finite F] in
/-- Any actual quotient equivalence marks the actor correctly: the
derived subgroup maps to A₅. This connects the two independent inputs
to the exact local-generation consumer. -/
theorem fiveGeometryAt_of_unmarked (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) (z : graphExtension F)
    (hgeometry : UnmarkedFiveGeometryAt F T Ω z)
    (hmodel : let K := PSUThreeGeneration.centralizerResidualOvergroup T z
      Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5))) :
    FiveGeometryAt F T Ω z := by
  rcases hgeometry with hsol | ⟨B, hB, hBT, hc, hout⟩
  · exact Or.inl hsol
  · obtain ⟨e⟩ := hmodel
    refine Or.inr ⟨B, hB, hBT, e, hc, ?_⟩
    intro hle
    apply hout
    have he : (_root_.commutator _).map e.toMonoidHom = alternatingGroup (Fin 5) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
      exact alternatingGroup.commutator_perm_eq (by simp)
    rw [← he] at hle
    exact (map_le_map_iff_of_injective e.injective).mp hle

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
