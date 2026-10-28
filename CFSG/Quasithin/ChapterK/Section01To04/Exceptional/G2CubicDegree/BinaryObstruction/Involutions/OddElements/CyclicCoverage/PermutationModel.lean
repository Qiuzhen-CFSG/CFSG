module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification.Geometry
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# A faithful coordinate action for the odd-element certificates

The existing bijection with the 63 parabolic cosets transports the actual
binary derived G₂ action to the published permutations. Simplicity and one
nontrivial generator prove that this action is faithful. Consequently small
permutation identities certify identities in the literal commutator subgroup.

The seven-word power is checked in this faithful action. The multiplication convention
is the existing left action, with the same two generators as `groupHom`.
This supports Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3,
pp.10–11. The underlying root and permutation data retain their attribution in
`VertexFiltrations.Coordinates` and `LICENSES/ATLAS.txt`.
-/

open G2DerivedPermutationFiltration G2DerivedPermutationFiltration.VertexCoordinates
open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverageCertificate
abbrev Actor := commutator (Atlas.G2.Model (ZMod 2))

def coordinateEquiv : Fin 63 ≃ Vertex 0 := Equiv.ofBijective (vertex 0) (vertex_bijective 0)

def action : Actor →* Equiv.Perm (Fin 63) :=
  (Equiv.permCongrHom coordinateEquiv.symm).toMonoidHom.comp (vertexPerm 0)

theorem action_generator (j : Fin 2) : action (groupGenerator j) = generator 0 j := by
  apply Equiv.ext
  intro x
  apply coordinateEquiv.injective
  change coordinateEquiv (coordinateEquiv.symm (vertexPerm 0 (groupGenerator j) (coordinateEquiv x))) = _
  rw [coordinateEquiv.apply_symm_apply]
  exact (vertex_generator_action 0 j x).symm

theorem action_injective : Function.Injective action := by
  let : IsSimpleGroup Actor := Atlas.G2.isSimple_commutator_binary
  apply action.ker_eq_bot_iff.mp
  rcases (inferInstance : action.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have he : action (groupGenerator 0) = 1 :=
      MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top _)
    rw [action_generator] at he
    have := congrArg (fun p : Equiv.Perm (Fin 63) => p 0) he
    contradiction

def eval (w : List (Fin 2)) : Actor := (w.map groupGenerator).prod

def perm (w : List (Fin 2)) : Equiv.Perm (Fin 63) := (w.map (generator 0)).prod

theorem action_eval (w : List (Fin 2)) : action (eval w) = perm w := by
  simp only [eval, perm, map_list_prod, List.map_map, Function.comp_def, action_generator]

theorem seven_pow : (groupGenerator 0 * (groupGenerator 1)⁻¹)^7 = 1 := by
  apply action_injective
  simp only [map_pow, map_mul, map_inv, map_one, action_generator]
  decide +kernel

theorem seven_ne_one : groupGenerator 0 * (groupGenerator 1)⁻¹ ≠ 1 := by
  intro h
  have he := congrArg action h
  simp only [map_mul, map_inv, map_one, action_generator] at he
  have hx := congrArg (fun p : Equiv.Perm (Fin 63) => p 0) he
  exact (by decide +kernel : (generator 0 0 * (generator 0 1)⁻¹) 0 ≠ 0) hx

/-- The marked seven-element has its exact prime order in the actual actor. -/
theorem seven_order : orderOf (groupGenerator 0 * (groupGenerator 1)⁻¹) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime seven_pow seven_ne_one

/-- The actual commutator group has order 6048. -/
theorem card_actor : Nat.card Actor = 6048 := by
  rw [show Actor = Atlas.G2.BinaryException.H from
    Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverageCertificate
