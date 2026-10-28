module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.LocalCycles

/-!
# The rank-three path-presentation theorem

If translated local cycles form a normal cycle base, the canonical map from
the rank-three presentation to the acting group is an isomorphism. The proof
uses the connected coset graph, local bijectivity of its projection, and closed
lifting of the actual translated local generators. The existing normal-cycle
transport theorem then makes the coset projection injective, which detects the
kernel of the canonical group map.

Consequently every compatible triple of homomorphisms on the vertex, setwise
edge, and local groups extends uniquely to the acting group. No simple
connectivity assumption or global extension hypothesis is added.

Source: Aschbacher, *Sporadic Groups* (1994), 35.16 and 37.4–37.5.
-/

@[expose] public section
namespace Theory.GroupTheory.GraphUniquenessSystem.System

universe u v w
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable (U : System G V)

namespace PathPresentation

/-- A normal cycle base makes the canonical rank-three presentation map bijective. -/
theorem canonical_bijective_of_isBase (hb : U.IsBase) :
    Function.Bijective (canonical U) := by
  obtain ⟨t, htx, hty⟩ := U.exists_swap
  exact canonical_bijective_of_cover U t htx hb
    (cosetGraph_preconnected U t htx hty)
    (neighbor_bijective U t htx hty)
    (baseCycles_transport U t htx (neighbor_bijective U t htx hty))

/-- The path-presentation isomorphism supplied by the normal cycle base. -/
noncomputable def equivOfBase (hb : U.IsBase) : U.PathPresentation ≃* G :=
  MulEquiv.ofBijective (canonical U) (canonical_bijective_of_isBase U hb)

@[simp] theorem equivOfBase_apply (hb : U.IsBase) (p : U.PathPresentation) :
    equivOfBase U hb p = canonical U p := rfl

@[simp] theorem equivOfBase_symm_vertex (hb : U.IsBase) (a : U.vertexGroup) :
    (equivOfBase U hb).symm a = vertex U a := by
  apply (equivOfBase U hb).injective
  simp

@[simp] theorem equivOfBase_symm_edge (hb : U.IsBase) (a : U.edgeSetGroup) :
    (equivOfBase U hb).symm a = edge U a := by
  apply (equivOfBase U hb).injective
  simp

@[simp] theorem equivOfBase_symm_local (hb : U.IsBase) (a : U.H) :
    (equivOfBase U hb).symm a = localMap U a := by
  apply (equivOfBase U hb).injective
  simp

end PathPresentation

namespace AmalgamMap
variable {U} {K : Type w} [Group K] (m : U.AmalgamMap K)

/-- Compatible maps on all three groups extend over a system with a cycle base. -/
noncomputable def liftOfBase (hb : U.IsBase) : m.Lift where
  hom := (PathPresentation.lift U m).comp
    (PathPresentation.equivOfBase U hb).symm.toMonoidHom
  onVertex a := by
    change PathPresentation.lift U m ((PathPresentation.equivOfBase U hb).symm a) = _
    rw [PathPresentation.equivOfBase_symm_vertex, PathPresentation.lift_vertex]
  onEdge a := by
    change PathPresentation.lift U m ((PathPresentation.equivOfBase U hb).symm a) = _
    rw [PathPresentation.equivOfBase_symm_edge, PathPresentation.lift_edge]
  onLocal a := by
    change PathPresentation.lift U m ((PathPresentation.equivOfBase U hb).symm a) = _
    rw [PathPresentation.equivOfBase_symm_local, PathPresentation.lift_local]

/-- Existence of a lift needs only the actual normal cycle base condition. -/
theorem nonempty_lift_of_isBase (hb : U.IsBase) : Nonempty m.Lift := ⟨m.liftOfBase hb⟩

/-- The extension of a compatible rank-three amalgam map is unique. -/
theorem existsUnique_hom_of_isBase (hb : U.IsBase) :
    ∃! f : G →* K,
      (∀ a : U.vertexGroup, f a = m.vertexHom a) ∧
      (∀ a : U.edgeSetGroup, f a = m.edgeHom a) ∧
      (∀ a : U.H, f a = m.localHom a) := by
  let f := m.liftOfBase hb
  refine ⟨f.hom, ⟨f.onVertex, f.onEdge, f.onLocal⟩, ?_⟩
  intro g hg
  exact Lift.hom_unique m (⟨g, hg.1, hg.2.1, hg.2.2⟩ : m.Lift) f

end AmalgamMap
end Theory.GroupTheory.GraphUniquenessSystem.System
