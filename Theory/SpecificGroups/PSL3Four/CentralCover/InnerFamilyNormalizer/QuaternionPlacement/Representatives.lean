module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Field
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.GraphField

/-!
# Quaternion placement for the three outer involution representatives

For the actual projective matrix group PSL₃(4), every quaternion subgroup
centralizing one of the field, graph or graph-field representatives lies in
the inner automorphism image joined with that representative's cyclic subgroup.
The field and graph cases follow from their constructed dihedral-times-C₂
Sylow models, which exclude quaternion subgroups. The graph-field case uses
the actual marked ternary matrix map, its three-group kernel and the computed
quaternion matrix fibers. All three structural inputs are discharged here.

Faithful automorphism transport gives the same conclusion for conjugates,
including inner conjugates. The imported `MulAut` transport lemmas preserve
order, outer status, full centralizers and the actual inner image. The
representative hypothesis is an equality with one of the three displayed
automorphisms; an arbitrary outer-involution classification is a separate input
for consumers that need to cover every outer involution.

Source: Aschbacher–Smith 16.1.4(4)–(6), printed pp.1171–1172, and the
quaternion containment in the proof of 16.4.9(2), printed p.1192,
`refs/quasithin.pdf` (combined manuscript of 1 March 2004).
-/

public section

open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement
open ExtendedCentralizer.ProjectiveFixer

/-- Quaternion placement in the full centralizer of the field involution. -/
theorem field_placement
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer pslFrobenius) : P ≤ innerWith pslFrobenius :=
  field_placement_of_sylow_model Field.sylow Field.sylowEquiv P hP hPC

/-- Quaternion placement in the full centralizer of the graph involution. -/
theorem graph_placement
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer (PSL3.OuterSolvable.graph F)) :
    P ≤ innerWith (PSL3.OuterSolvable.graph F) :=
  Graph.placement P hP hPC

/-- Quaternion placement in the full centralizer of the graph-field involution. -/
theorem graphField_placement
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer
      (PSL3.OuterSolvable.graph F * pslFrobenius)) :
    P ≤ innerWith (PSL3.OuterSolvable.graph F * pslFrobenius) :=
  graphField_placement_of_matrix_model GraphField.matrixMap
    GraphField.matrixMap_ker_isThreeGroup GraphField.matrixMap_fibers_inner P hP hPC

/-- All three actual representatives satisfy the quaternion containment. -/
theorem representative_placement (a : MulAut PSL)
    (ha : a = pslFrobenius ∨ a = PSL3.OuterSolvable.graph F ∨
      a = PSL3.OuterSolvable.graph F * pslFrobenius)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer a) : P ≤ innerWith a := by
  rcases ha with rfl | rfl | rfl
  · exact field_placement P hP hPC
  · exact graph_placement P hP hPC
  · exact graphField_placement P hP hPC

/-- Faithful conjugation transports the representative containment in the actual
automorphism group, with the actual inner image in the conclusion. -/
theorem representative_conjugate_placement (b a : MulAut PSL)
    (ha : a = pslFrobenius ∨ a = PSL3.OuterSolvable.graph F ∨
      a = PSL3.OuterSolvable.graph F * pslFrobenius)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer (b * a * b⁻¹)) :
    P ≤ innerWith (b * a * b⁻¹) :=
  MulAut.quaternion_centralizer_placement_conjugate b a
    (representative_placement a ha) P hP hPC

/-- The representative containment for conjugation by an element of PSL₃(4). -/
theorem representative_inner_conjugate_placement (g : PSL) (a : MulAut PSL)
    (ha : a = pslFrobenius ∨ a = PSL3.OuterSolvable.graph F ∨
      a = PSL3.OuterSolvable.graph F * pslFrobenius)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer (MulAut.conj g * a * (MulAut.conj g)⁻¹)) :
    P ≤ innerWith (MulAut.conj g * a * (MulAut.conj g)⁻¹) :=
  representative_conjugate_placement (MulAut.conj g) a ha P hP hPC

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement
