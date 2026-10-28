module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.Amalgam
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The rank-three presentation

Take generators from the vertex stabilizer, the setwise edge stabilizer, and
local group. Impose their multiplication tables and identify elements in each
of the three pairwise intersections. The resulting group has the universal
property for compatible maps of the rank-three amalgam. Its canonical map onto
the acting group is surjective and embeds each of the three constituent groups.
The cycle-base hypothesis is needed only for global injectivity.

Source: Aschbacher, *Sporadic Groups* (1994), §§35–37, especially 37.5.
-/

@[expose] public section
namespace Theory.GroupTheory.GraphUniquenessSystem.System

universe u v w
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable (U : System G V)

/-- Generators retain which of the three constituent groups they come from. -/
inductive PresentationGenerator
  | vertex : U.vertexGroup → PresentationGenerator
  | edge : U.edgeSetGroup → PresentationGenerator
  | localGen : U.H → PresentationGenerator

/-- Multiplication tables and all three pairwise intersection relations. -/
inductive PresentationRel : FreeGroup U.PresentationGenerator → Prop
  | vertex_mul (a b : U.vertexGroup) : PresentationRel
      (FreeGroup.of (.vertex (a * b)) *
        (FreeGroup.of (.vertex a) * FreeGroup.of (.vertex b))⁻¹)
  | edge_mul (a b : U.edgeSetGroup) : PresentationRel
      (FreeGroup.of (.edge (a * b)) *
        (FreeGroup.of (.edge a) * FreeGroup.of (.edge b))⁻¹)
  | local_mul (a b : U.H) : PresentationRel
      (FreeGroup.of (.localGen (a * b)) *
        (FreeGroup.of (.localGen a) * FreeGroup.of (.localGen b))⁻¹)
  | vertex_edge (g : G) (hv : g ∈ U.vertexGroup) (he : g ∈ U.edgeSetGroup) :
      PresentationRel (FreeGroup.of (.vertex ⟨g, hv⟩) * (FreeGroup.of (.edge ⟨g, he⟩))⁻¹)
  | local_vertex (g : G) (hh : g ∈ U.H) (hv : g ∈ U.vertexGroup) :
      PresentationRel (FreeGroup.of (.localGen ⟨g, hh⟩) * (FreeGroup.of (.vertex ⟨g, hv⟩))⁻¹)
  | local_edge (g : G) (hh : g ∈ U.H) (he : g ∈ U.edgeSetGroup) :
      PresentationRel (FreeGroup.of (.localGen ⟨g, hh⟩) * (FreeGroup.of (.edge ⟨g, he⟩))⁻¹)

/-- The universal group of the rank-three amalgam, before using the cycle base. -/
def PathPresentation := PresentedGroup {r | U.PresentationRel r}
  deriving Group

namespace PathPresentation

/-- Inclusion of the vertex group. -/
def vertex : U.vertexGroup →* U.PathPresentation :=
  MonoidHom.mk' (fun a => PresentedGroup.of (.vertex a)) fun a b =>
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (PresentationRel.vertex_mul a b)

/-- Inclusion of the setwise edge group. -/
def edge : U.edgeSetGroup →* U.PathPresentation :=
  MonoidHom.mk' (fun a => PresentedGroup.of (.edge a)) fun a b =>
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (PresentationRel.edge_mul a b)

/-- Inclusion of the local group. -/
def localMap : U.H →* U.PathPresentation :=
  MonoidHom.mk' (fun a => PresentedGroup.of (.localGen a)) fun a b =>
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (PresentationRel.local_mul a b)

/-- The three inclusions form a compatible amalgam map. -/
def inclusions : U.AmalgamMap U.PathPresentation where
  vertexHom := vertex U
  edgeHom := edge U
  localHom := localMap U
  vertex_edge g hv he :=
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (PresentationRel.vertex_edge g hv he)
  local_vertex g hh hv :=
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (PresentationRel.local_vertex g hh hv)
  local_edge g hh he :=
    PresentedGroup.mk_eq_mk_of_mul_inv_mem (PresentationRel.local_edge g hh he)

variable {K : Type w} [Group K]

/-- Evaluate each kind of generator under a compatible amalgam map. -/
def generatorMap (m : U.AmalgamMap K) : U.PresentationGenerator → K
  | .vertex a => m.vertexHom a
  | .edge a => m.edgeHom a
  | .localGen a => m.localHom a

/-- Every defining relation is respected by a compatible amalgam map. -/
theorem relations (m : U.AmalgamMap K) (r : FreeGroup U.PresentationGenerator)
    (hr : U.PresentationRel r) : FreeGroup.lift (generatorMap U m) r = 1 := by
  cases hr with
  | vertex_mul a b => simp [generatorMap]
  | edge_mul a b => simp [generatorMap]
  | local_mul a b => simp [generatorMap]
  | vertex_edge g hv he => simp [generatorMap, m.vertex_edge g hv he]
  | local_vertex g hh hv => simp [generatorMap, m.local_vertex g hh hv]
  | local_edge g hh he => simp [generatorMap, m.local_edge g hh he]

/-- The universal homomorphism out of the rank-three presentation. -/
def lift (m : U.AmalgamMap K) : U.PathPresentation →* K :=
  PresentedGroup.toGroup (relations U m)

@[simp] theorem lift_vertex (m : U.AmalgamMap K) (a : U.vertexGroup) :
    lift U m (vertex U a) = m.vertexHom a := PresentedGroup.toGroup.of _

@[simp] theorem lift_edge (m : U.AmalgamMap K) (a : U.edgeSetGroup) :
    lift U m (edge U a) = m.edgeHom a := PresentedGroup.toGroup.of _

@[simp] theorem lift_local (m : U.AmalgamMap K) (a : U.H) :
    lift U m (localMap U a) = m.localHom a := PresentedGroup.toGroup.of _

/-- Homomorphisms are determined by their values on the three constituent groups. -/
theorem hom_ext (f g : U.PathPresentation →* K)
    (hv : ∀ a, f (vertex U a) = g (vertex U a))
    (he : ∀ a, f (edge U a) = g (edge U a))
    (hh : ∀ a, f (localMap U a) = g (localMap U a)) : f = g := by
  apply PresentedGroup.ext
  intro a
  cases a with
  | vertex a => exact hv a
  | edge a => exact he a
  | localGen a => exact hh a

/-- Existence and uniqueness in the universal property, for arbitrary target groups. -/
theorem existsUnique_lift (m : U.AmalgamMap K) :
    ∃! f : U.PathPresentation →* K,
      (∀ a, f (vertex U a) = m.vertexHom a) ∧
      (∀ a, f (edge U a) = m.edgeHom a) ∧
      (∀ a, f (localMap U a) = m.localHom a) := by
  refine ⟨lift U m, ⟨lift_vertex U m, lift_edge U m, lift_local U m⟩, ?_⟩
  intro f hf
  exact hom_ext U f (lift U m)
    (fun a => (hf.1 a).trans (lift_vertex U m a).symm)
    (fun a => (hf.2.1 a).trans (lift_edge U m a).symm)
    (fun a => (hf.2.2 a).trans (lift_local U m a).symm)

/-- Inclusion of the actual subgroups into the acting group. -/
def ambientMap : U.AmalgamMap G where
  vertexHom := U.vertexGroup.subtype
  edgeHom := U.edgeSetGroup.subtype
  localHom := U.H.subtype
  vertex_edge _ _ _ := rfl
  local_vertex _ _ _ := rfl
  local_edge _ _ _ := rfl

/-- The canonical homomorphism from the presentation to the acting group. -/
def canonical : U.PathPresentation →* G := lift U (ambientMap U)

@[simp] theorem canonical_vertex (a : U.vertexGroup) : canonical U (vertex U a) = a :=
  lift_vertex U (ambientMap U) a

@[simp] theorem canonical_edge (a : U.edgeSetGroup) : canonical U (edge U a) = a :=
  lift_edge U (ambientMap U) a

@[simp] theorem canonical_local (a : U.H) : canonical U (localMap U a) = a :=
  lift_local U (ambientMap U) a

/-- The canonical homomorphism is onto, using generation in the uniqueness system. -/
theorem canonical_surjective : Function.Surjective (canonical U) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← U.generate]
  exact sup_le
    (fun a ha => ⟨localMap U ⟨a, ha⟩, canonical_local U ⟨a, ha⟩⟩)
    (fun a ha => ⟨vertex U ⟨a, ha⟩, canonical_vertex U ⟨a, ha⟩⟩)

/-- Each constituent embeds, since its composite with the canonical map is inclusion. -/
theorem vertex_injective : Function.Injective (vertex U) := by
  intro a b h
  apply Subtype.ext
  simpa only [canonical_vertex] using congrArg (canonical U) h

/-- The setwise edge constituent embeds. -/
theorem edge_injective : Function.Injective (edge U) := by
  intro a b h
  apply Subtype.ext
  simpa only [canonical_edge] using congrArg (canonical U) h

/-- The local constituent embeds. -/
theorem local_injective : Function.Injective (localMap U) := by
  intro a b h
  apply Subtype.ext
  simpa only [canonical_local] using congrArg (canonical U) h

/-- The three constituent images generate the presentation. -/
theorem generate : (vertex U).range ⊔ (edge U).range ⊔ (localMap U).range = ⊤ := by
  apply top_unique
  intro p _
  apply PresentedGroup.generated_by _ _ _ p
  intro a
  cases a with
  | vertex a => exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨a, rfl⟩)
  | edge a => exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨a, rfl⟩)
  | localGen a => exact Subgroup.mem_sup_right ⟨a, rfl⟩

end PathPresentation
end Theory.GroupTheory.GraphUniquenessSystem.System
