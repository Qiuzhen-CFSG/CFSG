module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Setup
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.ApartmentCycle
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.Girth
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.CycleConjugacy

/-!
# Comparison with the marked BN-pair coset geometry

Both vertex subgroups are the singleton standard parabolics of the concrete
Tits system. A marked Weyl isomorphism therefore supplies the algebraic data
for the abstract dihedral geometry without changing vertices, incidence,
normalizer apartments, or the action of the full Ree group.

The marked dihedral construction makes the normalizer apartment a simple
sixteen-cycle. Bruhat coverage gives diameter at most eight, and reduced
alternating galleries give girth at least sixteen. The resulting uniqueness
of short paths identifies every sixteen-cycle with an actual apartment
translate. Thus the marked Weyl isomorphism alone supplies the remaining
input to both geometric conclusions for `1 ≤ m`.

Source: GLS3 §§2.3 and 2.6, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

open Subgroup LargeLocalSeeds Parabolics SectionGeometry.BNPair
open Theory.AlgebraicGroup.TitsSystem
open scoped Pointwise

attribute [local instance] borel_inf_normalizerWords_normal

/-- The abstract graph is the existing full-parabolic incidence graph. -/
theorem incidenceGraph_eq_dihedralGraph (m : ℕ) :
    incidenceGraph m = DihedralGeometry.graph (ConverseParabolics.parabolic m) := rfl

/-- The abstract apartment is precisely the published normalizer-word orbit. -/
theorem standardApartment_eq_dihedralApartment (m : ℕ) :
    standardApartment m =
      DihedralGeometry.apartment (titsSystem m) (ConverseParabolics.parabolic m) := rfl

/-- The marked quotient and the two proved parabolic identifications give all
algebraic hypotheses of the dihedral coset-geometry construction. -/
theorem exists_octagonalDatum (m : ℕ) (hm : 1 ≤ m) (hW : HasOctagonalWeylGroup m) :
    Nonempty (DihedralGeometry.OctagonalDatum
      (titsSystem m) (ConverseParabolics.parabolic m)) := by
  obtain ⟨e, he₀, he₁⟩ := hW
  refine ⟨{
    typeEquiv := {
      toFun := fun s => match s with | .linear => false | .suzuki => true
      invFun := fun b => if b then .suzuki else .linear
      left_inv := by intro s; cases s <;> rfl
      right_inv := by intro b; cases b <;> rfl }
    simple := simpleReflection m
    simple_range := rfl
    weylEquiv := e
    map_simple := ?_
    parabolic_eq := fun s => (standardParabolic_singleton_eq_parabolic m hm s).symm
  }⟩
  intro s
  cases s with
  | linear => exact he₀
  | suzuki => exact he₁

private theorem borel_le_vertex_parabolic (m : ℕ) (s : Side) :
    (titsSystem m).B ≤ ConverseParabolics.parabolic m s := by
  rw [parabolic_eq_rootParabolic]
  exact Parabolics.borel_le_parabolic m s

/-- Every pair of actual edges lies in one translate of the specified standard
apartment. This uses Bruhat coverage, with no metric or simplicity hypothesis. -/
theorem exists_standardApartment_translate_for_edges {m : ℕ}
    {v₁ v₂ w₁ w₂ : Vertex m}
    (hv : (incidenceGraph m).Adj v₁ v₂) (hw : (incidenceGraph m).Adj w₁ w₂) :
    ∃ g : Model m, v₁ ∈ g • standardApartment m ∧ v₂ ∈ g • standardApartment m ∧
      w₁ ∈ g • standardApartment m ∧ w₂ ∈ g • standardApartment m :=
  DihedralGeometry.exists_apartment_for_edges (ConverseParabolics.parabolic m)
    (titsSystem m) (borel_le_vertex_parabolic m) hv hw

/-- Every pair of actual vertices lies in a translate of the same normalizer
orbit, retaining the full Ree group action. -/
theorem exists_standardApartment_translate_for_vertices (m : ℕ) (v w : Vertex m) :
    ∃ g : Model m, v ∈ g • standardApartment m ∧ w ∈ g • standardApartment m :=
  DihedralGeometry.exists_apartment_for_vertices (ConverseParabolics.parabolic m)
    (titsSystem m) (borel_le_vertex_parabolic m) v w

/-- The marked concrete Weyl quotient gives diameter at most eight, girth at
least sixteen, and a simple sixteen-cycle in the actual full-parabolic graph. -/
theorem octagonGeometry_of_weyl (m : ℕ) (hm : 1 ≤ m) (hW : HasOctagonalWeylGroup m) :
    OctagonGeometry m := by
  obtain ⟨D⟩ := exists_octagonalDatum m hm hW
  have hA := D.standardApartmentCycle
  refine ⟨?_, D.cycle_bound, ?_⟩
  · exact DihedralGeometry.diameter_bound_of_standardApartmentCycle
      (ConverseParabolics.parabolic m) (titsSystem m) D.borel_le hA
  · obtain ⟨v, p, hp, hlen, _⟩ := hA
    exact ⟨v, p, hp, hlen⟩

/-- Every simple sixteen-cycle is a translate of the specified normalizer-word
apartment under the original full Ree group action. -/
theorem apartmentTranslates_of_weyl (m : ℕ) (hm : 1 ≤ m) (hW : HasOctagonalWeylGroup m) :
    ApartmentTranslates m := by
  obtain ⟨D⟩ := exists_octagonalDatum m hm hW
  exact D.apartment_translates_of_cycle_bound D.standardApartmentCycle D.cycle_bound

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
