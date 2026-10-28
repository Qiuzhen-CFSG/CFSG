module

public import Theory.Representation.G2DerivedPermutationFiltration.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Levi

/-!
# The binary parabolic incidence map for G₂(2)′

Chambers are the actual unipotent cosets from `Basic`. The two vertex sets
are the cosets of the standard full parabolics, each of size 63. Forgetting
one endpoint is equivariant for the actual derived group. Linear extension
of the two projection maps gives the boundary from the 189-dimensional
chamber module into the product of the vertex permutation modules.

The kernel is the actual invariant cycle space, defined without a character
table or a proposed list of constituents. Filtrations of the two vertex
modules and of this kernel will give a filtration of the chamber module by
submodule and extension closure. Those finite constituent calculations are
separate obligations; neither irreducibility nor a filtration is assumed or
asserted here.

This decomposition supports Aschbacher–Smith G.7.2(3), printed p.348
(PDF p.359). Root groups and parabolics are those of the attributed ATLAS
ports imported above; no additional ATLAS source is copied here.
-/

@[expose] public section

open Atlas.G2 Representation
namespace G2DerivedPermutationFiltration

/-- The two standard full parabolics containing the fixed unipotent subgroup. -/
def parabolic (i : Fin 2) : Subgroup FullGroup :=
  if i = 0 then BinaryParabolicPair.firstParabolic else BinaryCore.secondParabolic

theorem unipotent_le_parabolic (i : Fin 2) : unipotent (K := ZMod 2) ≤ parabolic i := by
  unfold parabolic
  split
  · exact BinaryParabolicPair.unipotent_le_firstParabolic
  · exact Atlas.G2.unipotent_le_parabolic

theorem card_parabolic (i : Fin 2) : Nat.card (parabolic i) = 192 := by
  unfold parabolic
  split
  · exact BinaryParabolicPair.card_firstParabolic
  · exact BinaryCore.secondParabolic_card

abbrev Vertex (i : Fin 2) := FullGroup ⧸ parabolic i
noncomputable instance (i : Fin 2) : Fintype (Vertex i) := Fintype.ofFinite (Vertex i)

def vertexPerm (i : Fin 2) : Group →* Equiv.Perm (Vertex i) :=
  (MulAction.toPermHom FullGroup (Vertex i)).comp Group.subtype

def vertexRepresentation (i : Fin 2) :
    Representation (ZMod 2) Group (BinaryPermutation.Full (Vertex i)) :=
  (BinaryPermutation.representation (Vertex i)).comp (vertexPerm i)

theorem card_vertices (i : Fin 2) : Fintype.card (Vertex i) = 63 := by
  have hc := (parabolic i).card_mul_index
  have hg : Nat.card FullGroup = 12096 := by
    rw [Atlas.G2.card_Model, Nat.card_eq_fintype_card, ZMod.card]
    norm_num
  rw [card_parabolic, hg] at hc
  change 192 * Nat.card (Vertex i) = 12096 at hc
  rw [Nat.card_eq_fintype_card] at hc
  omega

/-- Forget one endpoint of a chamber, on literal ambient cosets. -/
def projection (i : Fin 2) : Flag → Vertex i :=
  Subgroup.quotientMapOfLE (unipotent_le_parabolic i)

@[simp] theorem projection_mk (i : Fin 2) (g : FullGroup) :
    projection i (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

theorem projection_action (i : Fin 2) (g : Group) (f : Flag) :
    projection i (flagPerm g f) = vertexPerm i g (projection i f) := by
  induction f using Quotient.inductionOn
  rfl

noncomputable def vertexBasis (i : Fin 2) (v : Vertex i) : BinaryPermutation.Full (Vertex i) := by
  classical
  exact Pi.single v 1

theorem vertexBasis_action (i : Fin 2) (g : Group) (v : Vertex i) :
    vertexBasis i (vertexPerm i g v) = vertexRepresentation i g (vertexBasis i v) := by
  classical
  ext w
  change (Pi.single (vertexPerm i g v) (1 : ZMod 2) : Vertex i → ZMod 2) w =
    (Pi.single v 1 : Vertex i → ZMod 2) ((vertexPerm i g).symm w)
  simp [Pi.single_apply, Equiv.symm_apply_eq]

noncomputable def pushForwardLinear (i : Fin 2) :
    BinaryPermutation.Full Flag →ₗ[ZMod 2] BinaryPermutation.Full (Vertex i) where
  toFun a := ∑ f : Flag, a f • vertexBasis i (projection i f)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [smul_smul, Finset.smul_sum]

/-- Push forward coefficients along the chamber-to-vertex projection. -/
noncomputable def pushForward (i : Fin 2) :
    flagRepresentation.IntertwiningMap (vertexRepresentation i) where
  toLinearMap := pushForwardLinear i
  isIntertwining' g := by
    apply LinearMap.ext
    intro a
    change (∑ f : Flag, a ((flagPerm g).symm f) • vertexBasis i (projection i f)) =
      vertexRepresentation i g (∑ f : Flag, a f • vertexBasis i (projection i f))
    rw [← Equiv.sum_comp (flagPerm g) (fun f : Flag =>
      a ((flagPerm g).symm f) • vertexBasis i (projection i f))]
    simp only [Equiv.symm_apply_apply, projection_action, vertexBasis_action, map_sum, map_smul]

@[simp] theorem pushForward_apply (i : Fin 2) (a : BinaryPermutation.Full Flag) :
    pushForward i a = ∑ f : Flag, a f • vertexBasis i (projection i f) := rfl

theorem pushForward_basis [DecidableEq Flag] (i : Fin 2) (f : Flag) :
    pushForward i (Pi.single f 1) = vertexBasis i (projection i f) := by
  classical
  rw [pushForward_apply]
  simp [Pi.single_apply]

/-- The direct sum of the two actual vertex permutation modules. -/
noncomputable def vertexPairRepresentation := (vertexRepresentation 0).prod (vertexRepresentation 1)

/-- The binary incidence boundary sends a flag to its two endpoints. -/
noncomputable def boundary : flagRepresentation.IntertwiningMap vertexPairRepresentation :=
  (pushForward 0).prod (pushForward 1)

/-- The cycle subrepresentation in the actual binary flag module. -/
noncomputable def cycleSubrepresentation : Subrepresentation flagRepresentation := boundary.ker

@[simp] theorem mem_cycleSubrepresentation (a : BinaryPermutation.Full Flag) :
    a ∈ cycleSubrepresentation ↔ pushForward 0 a = 0 ∧ pushForward 1 a = 0 := by
  change (pushForward 0 a, pushForward 1 a) = (0, 0) ↔ _
  simp only [Prod.mk.injEq]

theorem finrank_flagSpace : Module.finrank (ZMod 2) (BinaryPermutation.Full Flag) = 189 := by
  rw [Module.finrank_pi, card_flags]

theorem finrank_vertexSpace (i : Fin 2) :
    Module.finrank (ZMod 2) (BinaryPermutation.Full (Vertex i)) = 63 := by
  rw [Module.finrank_pi, card_vertices]

end G2DerivedPermutationFiltration
