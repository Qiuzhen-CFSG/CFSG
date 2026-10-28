/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3HeptadDot.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3LocalCounts
public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadIntersections
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3HeptadDot.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance co3HeptadDotPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

def co3HeptadEndpoint (a : Omega) (B : Co3Heptads a) : leech :=
  (co3EvenEndpointMap a (Sum.inr B)).val

theorem co3HeptadEndpoint_injective (a : Omega) : Function.Injective (co3HeptadEndpoint a) := by
  intro B C he
  apply Sum.inr.inj
  apply co3EvenEndpointMap_injective a
  exact Subtype.ext he

theorem co3HeptadEndpoint_apply (a : Omega) (B : Co3Heptads a) (i : Omega) :
    (co3HeptadEndpoint a B).val i = if i = a ∨ i ∈ mathieu23BlockLift a B.val then 2 else 0 := by
  simp [co3HeptadEndpoint,co3EvenEndpointMap,co3OctadEndpoint,constantSupportVector]

theorem co3HeptadEndpoint_marked (a : Omega) (B : Co3Heptads a) :
    (co3HeptadEndpoint a B).val a = 2 := by simp [co3HeptadEndpoint_apply]

theorem co3HeptadEndpoint_other (a : Omega) (B : Co3Heptads a) (b : Mathieu23Points a) :
    (co3HeptadEndpoint a B).val b.val = if b ∈ B.val then 2 else 0 := by
  simp [co3HeptadEndpoint_apply,mathieu23BlockLift,(show b.val ≠ a from b.prop)]

theorem co3Point_heptad_dot (a : Omega) (b : Mathieu23Points a) (B : Co3Heptads a) :
    integerDot (minimumPairPlus a b.val).val (co3HeptadEndpoint a B).val =
      if b ∈ B.val then 16 else 8 := by
  rw [minimumPairPlus_dot,co3HeptadEndpoint_marked,co3HeptadEndpoint_other]
  split_ifs <;> norm_num

theorem co3NormSix_heptad_dot (a : Omega) (B : Co3Heptads a) :
    integerDot (normSixVector a).val (co3HeptadEndpoint a B).val = 24 :=
  normSix_decomposition_dot a _ (co3EvenEndpointMap a (Sum.inr B)).prop.1
    (co3EvenEndpointMap a (Sum.inr B)).prop.2.1

theorem constantSupport_dot (k l : ℤ) (S T : Finset Omega) :
    integerDot (constantSupportVector k S) (constantSupportVector l T) = k*l*(S ∩ T).card := by
  have he (i : Omega) : constantSupportVector k S i*constantSupportVector l T i =
      if i ∈ S ∩ T then k*l else 0 := by
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [constantSupportVector,hs,ht]
  simp only [integerDot,he]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  ring

theorem co3Heptad_dot (a : Omega) (B C : Co3Heptads a) :
    integerDot (co3HeptadEndpoint a B).val (co3HeptadEndpoint a C).val =
      4*((B.val ∩ C.val).card+1) := by
  change integerDot (constantSupportVector 2 (insert a (mathieu23BlockLift a B.val)))
    (constantSupportVector 2 (insert a (mathieu23BlockLift a C.val))) = _
  rw [constantSupport_dot,← Finset.insert_inter_distrib,← mathieu23BlockLift_inter,
    Finset.card_insert_of_notMem (mathieu23BlockLift_not_mem _ _),mathieu23BlockLift_card]
  push_cast
  ring

theorem integerDot_sub_left (x y z : IntegerCoordinates) :
    integerDot (x-y) z = integerDot x z-integerDot y z := by
  simp [integerDot,sub_mul,Finset.sum_sub_distrib]

theorem integerDot_sub_right (x y z : IntegerCoordinates) :
    integerDot x (y-z) = integerDot x y-integerDot x z := by
  simp [integerDot,mul_sub,Finset.sum_sub_distrib]

theorem co3Heptad_complement_dot (a : Omega) (B C : Co3Heptads a) :
    integerDot (normSixVector a-co3HeptadEndpoint a B).val (co3HeptadEndpoint a C).val =
      24-4*((B.val ∩ C.val).card+1) := by
  change integerDot ((normSixVector a).val-(co3HeptadEndpoint a B).val) _ = _
  rw [integerDot_sub_left,co3NormSix_heptad_dot,co3Heptad_dot]

theorem co3Point_heptad_complement_dot (a : Omega) (b : Mathieu23Points a) (B : Co3Heptads a) :
    integerDot (minimumPairPlus a b.val).val (normSixVector a-co3HeptadEndpoint a B).val =
      if b ∈ B.val then 8 else 16 := by
  change integerDot _ ((normSixVector a).val-(co3HeptadEndpoint a B).val) = _
  rw [integerDot_sub_right,co3Point_heptad_dot,minimumPairPlus_dot,normSixVector_apply,normSixVector_apply]
  have hb : b.val ≠ a := b.prop
  simp only [ite_true,if_neg hb]
  split_ifs <;> norm_num

end Atlas.Conway
