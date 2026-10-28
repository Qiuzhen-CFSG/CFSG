module
public import Theory.Mathieu.M23.QuasithinGeometry.StandardSystem
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.GroupTheory.GraphUniquenessSystem.Recognition

/-!
# Ambient recognition from compatible heptad and vertex markings

Restrict one heptad marking to the four-set local subgroup. Its images of the
whole vertex intersection and setwise edge intersection give the local clauses
of a uniqueness-system similarity. A vertex marking agreeing on every element
of the intersection supplies the remaining clauses. Edge-fixer rigidity and the
native M23 cycle base then give the unique ambient equivalence extending both
markings. The source system retains all three actual generation identities.

These are conditional recognition results: the compatible vertex marking is an
input, not a consequence of an abstract pair-stabilizer isomorphism.
Source: Aschbacher--Smith, proof of Theorem 5.2.10, printed pp.657--658;
Aschbacher, Sporadic Groups, 37.9 and Exercise 13.1(b).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace Theory.GroupTheory.QuasithinM23
variable {G : Type*} [Group G]

private def markedLocalIso {V : Type*} [MulAction G V]
    (U : System G V) (J : Subgroup G) (hUJ : U.H ≤ J)
    (ζ : J ≃* heptadStabilizer)
    (hIm : (U.H.subgroupOf J).map ζ.toMonoidHom =
      fourStabilizer.subgroupOf heptadStabilizer) : U.H ≃* standardSystem.H :=
  (subgroupOfEquivOfLe hUJ).symm.trans
    ((ζ.subgroupMap (U.H.subgroupOf J)).trans
      ((MulEquiv.subgroupCongr hIm).trans
        (subgroupOfEquivOfLe fourStabilizer_le)))

private theorem markedLocalIso_coe {V : Type*} [MulAction G V]
    (U : System G V) (J : Subgroup G) (hUJ : U.H ≤ J)
    (ζ : J ≃* heptadStabilizer)
    (hIm : (U.H.subgroupOf J).map ζ.toMonoidHom =
      fourStabilizer.subgroupOf heptadStabilizer) (a : U.H) :
    (markedLocalIso U J hUJ ζ hIm a : Sporadic.Mathieu.M23) =
      (ζ ⟨a,hUJ a.property⟩ : Sporadic.Mathieu.M23) := rfl

private theorem marked_intersection_mem
    (I R J : Subgroup G) (hIJ : I ≤ J) (ζ : J ≃* heptadStabilizer)
    (P : Subgroup Sporadic.Mathieu.M23)
    (hm : ((I ⊓ R).subgroupOf J).map ζ.toMonoidHom =
      P.subgroupOf heptadStabilizer) (a : I) :
    (a : G) ∈ R ↔ (ζ ⟨a,hIJ a.property⟩ : Sporadic.Mathieu.M23) ∈ P := by
  have hh := mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective
    (K := (I ⊓ R).subgroupOf J) (x := ⟨a,hIJ a.property⟩)
  rw [hm] at hh
  exact (and_iff_right a.property).symm.trans hh.symm

/-- The same heptad marking and a vertex marking agreeing on the entire
intersection give a similarity of the original systems. -/
theorem heptad_marked_similarity {V : Type*} [MulAction G V]
    (U : System G V) (J : Subgroup G) (hUJ : U.H ≤ J)
    (ζ : J ≃* heptadStabilizer)
    (hIm : (U.H.subgroupOf J).map ζ.toMonoidHom =
      fourStabilizer.subgroupOf heptadStabilizer)
    (hvM : ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer)
    (hesM : ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
      fourEdgeStabilizer.subgroupOf heptadStabilizer)
    (β : U.vertexGroup ≃* pairStabilizer)
    (hagree : ∀ r : (U.H ⊓ U.vertexGroup : Subgroup G),
      (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
        (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23))
    (hedge : ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃ s : Similarity U standardSystem,
      (∀ a : U.vertexGroup, (s.vertexIso a : Sporadic.Mathieu.M23) = β a) ∧
      ∀ a : U.H, (s.localIso a : Sporadic.Mathieu.M23) = ζ ⟨a,hUJ a.property⟩ := by
  let v : U.vertexGroup ≃* standardSystem.vertexGroup :=
    β.trans (MulEquiv.subgroupCongr standardSystem_vertexGroup.symm)
  let l := markedLocalIso U J hUJ ζ hIm
  have hl (a : U.H) : (l a : Sporadic.Mathieu.M23) = ζ ⟨a,hUJ a.property⟩ := rfl
  have hlocal (a : U.H) : (a : G) ∈ U.vertexGroup ↔
      (l a : Sporadic.Mathieu.M23) ∈ standardSystem.vertexGroup := by
    have hh := marked_intersection_mem U.H U.vertexGroup J hUJ ζ fourPairStabilizer hvM a
    rw [←hl,←standardSystem_local_vertex] at hh
    exact hh.trans (and_iff_right (l a).property)
  have hlocalEdge (a : U.H) : (a : G) ∈ U.edgeSetGroup ↔
      (l a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeSetGroup := by
    have hh := marked_intersection_mem U.H U.edgeSetGroup J hUJ ζ fourEdgeStabilizer hesM a
    rw [←hl,←standardSystem_local_edgeStabilizer] at hh
    exact hh.trans (and_iff_right (l a).property)
  let s : Similarity U standardSystem := {
    vertexIso := v
    localIso := l
    agree := fun g hgH hgx => hagree ⟨g,hgH,hgx⟩
    local_vertex := hlocal
    edge := hedge
    local_edge := hlocalEdge }
  refine ⟨s,?_,hl⟩
  intro a
  rfl

/-- Edge rigidity and the native cycle base turn the compatible markings into
an actual ambient equivalence, with both local restrictions prescribed. -/
theorem heptad_marked_recognition {V : Type*} [MulAction G V]
    (U : System G V) (J : Subgroup G) (hUJ : U.H ≤ J)
    (ζ : J ≃* heptadStabilizer)
    (hIm : (U.H.subgroupOf J).map ζ.toMonoidHom =
      fourStabilizer.subgroupOf heptadStabilizer)
    (hvM : ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer)
    (hesM : ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
      fourEdgeStabilizer.subgroupOf heptadStabilizer)
    (hrigid : AutomorphismRigid (U.H.subgroupOf U.edgeGroup))
    (β : U.vertexGroup ≃* pairStabilizer)
    (hagree : ∀ r : (U.H ⊓ U.vertexGroup : Subgroup G),
      (β ⟨r,r.property.2⟩ : Sporadic.Mathieu.M23) =
        (ζ ⟨r,hUJ r.property.1⟩ : Sporadic.Mathieu.M23))
    (hedge : ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃! e : G ≃* Sporadic.Mathieu.M23,
      (∀ a : U.vertexGroup, e a = (β a : Sporadic.Mathieu.M23)) ∧
      (∀ a : U.H, e a = (ζ ⟨a,hUJ a.property⟩ : Sporadic.Mathieu.M23)) := by
  let := Sporadic.Mathieu.m23_isSimpleGroup
  obtain ⟨s,hv,hl⟩ := heptad_marked_similarity U J hUJ ζ hIm hvM hesM β hagree hedge
  obtain ⟨e,he,hu⟩ := s.existsUnique_mulEquiv_of_rigid_of_isBase hrigid standardSystem_isBase
  refine ⟨e,⟨fun a => (he.1 a).trans (hv a),fun a => (he.2 a).trans (hl a)⟩,?_⟩
  intro f hf
  exact hu f ⟨fun a => (hf.1 a).trans (hv a).symm,fun a => (hf.2 a).trans (hl a).symm⟩

end Theory.GroupTheory.QuasithinM23
