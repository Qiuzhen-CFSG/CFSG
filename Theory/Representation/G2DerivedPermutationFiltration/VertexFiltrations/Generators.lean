module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Coordinates

/-!
# The coordinate generators belong to the actual derived group

Each inverse GAP generator is a commutator of two explicit root words.
Equality is checked on the eight coordinate summands of the octonion carrier
by ordinary kernel reduction, then extended by linearity. Thus `groupHom`
has codomain literally `commutator (Atlas.G2.Model (ZMod 2))`.

The witness words were found using the exploratory calculation documented
in `Coordinates`. Generation of the whole derived group is a separate
obligation. This supports Aschbacher–Smith G.7.2(3), printed p.348.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.VertexCoordinates
open scoped commutatorElement

def commutatorFirst : Fin 2 → List (Fin 8 × ℤ) :=
  ![[(5,1),(2,1),(7,1),(6,1),(7,1),(0,1),(1,1),(2,1)],
    [(2,1),(4,1),(6,1),(7,1),(6,1),(7,1),(0,1),(1,1),(5,1),(6,-1),(4,-1)]]

def commutatorSecond : Fin 2 → List (Fin 8 × ℤ) :=
  ![[(6,-1),(4,-1),(5,-1),(1,-1),(7,-1),(6,-1),(7,-1),(5,-1)],
    [(4,-1),(1,-1),(7,-1),(6,-1),(7,-1),(6,-1),(7,-1),(3,-1)]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem generator_commutator_coordinates : ∀ (j : Fin 2) (b : Fin 8) (a : ZMod 2),
    (ambientGenerator j).val (Pi.single b a) =
      (⁅(evalWord (commutatorSecond j))⁻¹,
        (evalWord (commutatorFirst j))⁻¹⁆ : FullGroup).val (Pi.single b a) := by
  decide +kernel

theorem ambientGenerator_eq_commutator (j : Fin 2) :
    ambientGenerator j =
      ⁅(evalWord (commutatorSecond j))⁻¹, (evalWord (commutatorFirst j))⁻¹⁆ := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.pi_ext
  exact generator_commutator_coordinates j

theorem ambientGenerator_mem (j : Fin 2) : ambientGenerator j ∈ Group := by
  rw [ambientGenerator_eq_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

def groupGenerator (j : Fin 2) : Group := ⟨ambientGenerator j, ambientGenerator_mem j⟩

def groupHom : WordGroup →* Group := FreeGroup.lift groupGenerator

@[simp] theorem groupHom_of (j : Fin 2) :
    groupHom (FreeGroup.of j) = groupGenerator j := FreeGroup.lift_apply_of

theorem subtype_comp_groupHom : Group.subtype.comp groupHom = ambientWordHom := by
  apply FreeGroup.ext_hom
  intro j
  rfl

/-- The right-coset Schreier equation equivalent to a listed left-action entry.
This gives the precise multiplication order for checking the GAP table. -/
theorem vertex_generator_action_iff (i j : Fin 2) (x : Fin 63) :
    vertexPerm i (groupGenerator j) (vertex i x) = vertex i (generator i j x) ↔
      evalWord (representativeWord i x) * evalWord (generatorWord j) *
        (evalWord (representativeWord i (generator i j x)))⁻¹ ∈ parabolic i := by
  change QuotientGroup.mk
      ((evalWord (generatorWord j))⁻¹ * (evalWord (representativeWord i x))⁻¹) =
    (QuotientGroup.mk (evalWord (representativeWord i (generator i j x)))⁻¹ : Vertex i) ↔ _
  rw [QuotientGroup.eq]
  simp only [mul_inv_rev, inv_inv]

end G2DerivedPermutationFiltration.VertexCoordinates
