module
public import Theory.Representation.G2DerivedSixFactorMaps.NaturalMatrices
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations

/-!
# Nonzero maps from the eight six-dimensional literal factors

For each six-dimensional block of the two certified parabolic flags, a small
binary matrix intertwines its displayed generators with the natural matrices.
Lean checks these identities and nonvanishing by kernel reduction. Composing
with the existing literal quotient coordinates constructs actual intertwiners;
free-group induction proves their equivariance for every word. The surjective
group marking in the assembly then gives equivariance under G₂(2)′ itself.

The witness matrices were obtained by solving the two binary intertwining
systems using the existing factor matrices. No character table or recognition
hypothesis is used. Their action data derive from the attributed ATLAS ports
in `CoordinateFiltrations.Data`; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. Source: Aschbacher--Smith G.9.3(10), printed
pp.354,356--357. `source/GenerateMaps.py` reproduces the witness search;
only the Lean identities below certify its output.
-/

@[expose] public section
namespace G2DerivedSixFactorMaps
open G2DerivedPermutationFiltration.VertexCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Atlas.G2.Natural.Binary

def mapRows (i : Fin 2) (t : Factor i) : Fin 6 → ℕ :=
  match i.val, t.val with
  | 0, 1 => ![47,56,21,33,30,1]
  | 0, 3 => ![42,60,13,36,20,34]
  | 0, 6 => ![31,51,32,59,21,15]
  | 1, 0 => ![9,5,3,33,17,1]
  | 1, 3 => ![16,10,28,41,25,61]
  | 1, 5 => ![15,29,11,21,35,2]
  | 1, 8 => ![24,21,11,34,42,25]
  | 1, 10 => ![63,16,32,61,59,55]
  | _, _ => 0

/-- Candidate matrices from each literal factor to the natural coordinates.
Only the eight six-dimensional factors have nonzero matrices. -/
def mapMatrix (i : Fin 2) (t : Factor i) :
    Matrix (Fin 6) (Fin (degree i t)) (ZMod 2) :=
  fun r s => bit (mapRows i t r) s.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The displayed maps intertwine the two actual generator matrices. -/
theorem mapMatrix_intertwines : ∀ (i : Fin 2) (t : Factor i) (j : Fin 2),
    mapMatrix i t * factorMatrix i t j = naturalMatrix j * mapMatrix i t := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Every six-dimensional factor has a nonzero displayed matrix. -/
theorem mapMatrix_ne_zero : ∀ (i : Fin 2) (t : Factor i),
    degree i t = 6 → mapMatrix i t ≠ 0 := by
  decide +kernel

private theorem free_intertwining {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) WordGroup V) (σ : Representation (ZMod 2) WordGroup W)
    (f : V →ₗ[ZMod 2] W)
    (hf : ∀ j v, f (ρ (FreeGroup.of j) v) = σ (FreeGroup.of j) (f v))
    (g : WordGroup) (v : V) : f (ρ g v) = σ g (f v) := by
  induction g using FreeGroup.induction_on generalizing v with
  | C1 => simp
  | of j => exact hf j v
  | inv_of j ih =>
    have h := congrArg (σ ((FreeGroup.of j)⁻¹)) (ih (ρ ((FreeGroup.of j)⁻¹) v))
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, inv_mul_cancel,
      map_one, Module.End.one_apply] using h.symm
  | mul a b ha hb =>
    simpa only [map_mul, Module.End.mul_apply] using
      (ha (ρ b v)).trans (congrArg (σ a) (hb v))

/-- The literal successive quotient of the already certified adapted flag. -/
noncomputable abbrev factorRepresentation (i : Fin 2) (t : Factor i) :=
  (within ((adaptedFlagCoordinates i).stage t.val)
    ((adaptedFlagCoordinates i).stage (t.val + 1))).quotientRepresentation

/-- Intertwiner on the literal quotient, with equivariance for every free word.
The surjective actual-group marking is applied in the vertex assembly. -/
noncomputable def quotientMap (i : Fin 2) (t : Factor i) :
    (factorRepresentation i t).IntertwiningMap (coordinateAction.comp groupHom) where
  toLinearMap := (mapMatrix i t).toLin'.comp ((adaptedFlagCoordinates i).coordinates t).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    refine free_intertwining (factorRepresentation i t) (coordinateAction.comp groupHom)
      ((mapMatrix i t).toLin'.comp ((adaptedFlagCoordinates i).coordinates t).toLinearMap) ?_ g v
    intro j v
    change (mapMatrix i t).mulVec
      ((adaptedFlagCoordinates i).coordinates t ((factorRepresentation i t) (FreeGroup.of j) v)) =
      coordinateAction (groupHom (FreeGroup.of j))
        ((mapMatrix i t).mulVec ((adaptedFlagCoordinates i).coordinates t v))
    rw [(adaptedFlagCoordinates i).generator_coordinates, groupHom_of, natural_generator]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mapMatrix_intertwines]

/-- The quotient intertwiner is nonzero on each six-dimensional simple factor. -/
theorem quotientMap_ne_zero (i : Fin 2) (t : Factor i) (hd : degree i t = 6) :
    quotientMap i t ≠ 0 := by
  intro hz
  apply mapMatrix_ne_zero i t hd
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := ((adaptedFlagCoordinates i).coordinates t).surjective x
  simpa [quotientMap] using congrArg (fun f : (factorRepresentation i t).IntertwiningMap
    (coordinateAction.comp groupHom) => f v) hz

end G2DerivedSixFactorMaps
