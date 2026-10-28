module
public import Theory.Representation.G2DerivedSixFactorMaps.FiltrationTools
public import Theory.Representation.G2DerivedSixFactorMaps.QuotientMaps
public import Theory.Representation.G2DerivedPermutationFiltration
/-!
# Natural-coordinate maps on the binary G₂(2)′ flag factors

The two verified parabolic flags have eight simple factors of dimension six.
Their explicit nonzero maps to the natural coordinates strengthen the existing
filtrations. Transport through the already certified, surjective root-word
marking gives maps equivariant under the whole actual commutator group.
The incidence kernel has only two degree-32 factors. Exact pullback along the
boundary therefore assembles a map-retaining filtration of the flag module.

All irreducibility, dimension, incidence and generation inputs are reused from
`G2DerivedPermutationFiltration`; only the natural intertwiners and their
assembly are new. Source: Aschbacher--Smith G.9.3(10), printed pp.354,356--357.
-/

public section
namespace G2DerivedSixFactorMaps
open G2DerivedPermutationFiltration
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Atlas.G2.Natural.Binary
open Representation

/-- The checked coordinate flags retain actual nonzero maps on all factors of degree six. -/
theorem coordinate_factorMapFiltration (i : Fin 2) :
    FactorMapFiltration (coordinateAction.comp groupHom) (representation i) := by
  apply FactorMapFiltration.of_flag (coordinateAction.comp groupHom)
    (length i) (adaptedFlagCoordinates i).stage
    (adaptedFlagCoordinates i).zero (adaptedFlagCoordinates i).last
    (adaptedFlagCoordinates i).mono
  · intro m hm
    exact adaptedFlag_quotient_irreducible i ⟨m, hm⟩
  · intro m hm hd
    let t : Factor i := ⟨m, hm⟩
    have ht : degree i t = 6 := by
      rw [← adaptedFlag_quotient_finrank i t]
      simpa only [Module.finrank_fin_fun] using hd
    exact ⟨quotientMap i t, quotientMap_ne_zero i t ht⟩

/-- The factor maps are equivariant under the entire actual derived group,
using the already proved surjectivity of the filtration's generator marking. -/
theorem vertex_factorMapFiltration (i : Fin 2) :
    FactorMapFiltration coordinateAction (vertexRepresentation i) := by
  let e : Fin 63 ≃ Vertex i := Equiv.ofBijective (vertex i) (vertex_bijective i)
  let el : Space ≃ₗ[ZMod 2] BinaryPermutation.Full (Vertex i) :=
    LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) e.symm
  apply FactorMapFiltration.transport coordinateAction groupHom groupHom_surjective
    (coordinate_factorMapFiltration i) (vertexRepresentation i) el
  intro g v
  ext y
  change v ((wordPerm i g).symm (e.symm y)) =
    v (e.symm ((vertexPerm i (groupHom g)).symm y))
  congr 1
  apply e.injective
  rw [e.apply_symm_apply]
  apply (vertexPerm i (groupHom g)).injective
  rw [Equiv.apply_symm_apply, ← vertex_word_equivariance i e
    (fun j x => vertex_generator_action i j x), Equiv.apply_symm_apply, e.apply_symm_apply]

/-- The incidence kernel has only degree-32 factors, so none needs a map to six coordinates. -/
theorem cycle_factorMapFiltration :
    FactorMapFiltration coordinateAction cycleSubrepresentation.toRepresentation := by
  have h : FactorDegreeFiltration {32} cycleSubrepresentation.toRepresentation := by
    apply FactorDegreeFiltration.step cycleCoordinates.half
    · apply CycleMatrixCriterion.simple_filtration (k := ZMod 2) (G := Group)
        (V := cycleCoordinates.half.toSubmodule) {32} cycleCoordinates.half.toRepresentation
        (cycleCoordinates.half_irreducible (CycleData.fullFactorAlgebra 0))
      rw [cycleCoordinates.finrank_half]
      rfl
    · exact cycleCoordinates.quotient_irreducible (CycleData.fullFactorAlgebra 1)
    · rw [cycleCoordinates.finrank_quotient]
      rfl
  exact FactorMapFiltration.of_degree coordinateAction h (by simp)

/-- The actual 189-dimensional flag action has nonzero natural-coordinate maps
on every simple factor of dimension six. No extra mathematical premise remains. -/
theorem flag_factorMapFiltration :
    FactorMapFiltration coordinateAction flagRepresentation :=
  FactorMapFiltration.of_ker boundary cycle_factorMapFiltration
    ((vertex_factorMapFiltration 0).prod (vertex_factorMapFiltration 1))

end G2DerivedSixFactorMaps
