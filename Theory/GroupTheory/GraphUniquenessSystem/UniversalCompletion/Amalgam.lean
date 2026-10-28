module

public import Theory.GroupTheory.GraphUniquenessSystem.CompletionMap

/-!
# The rank-three amalgam of a graph uniqueness system

The three groups are the vertex stabilizer, the setwise edge stabilizer, and the
local group. Maps on them must agree on all three pairwise intersections. The
setwise-edge group is the union of the pointwise-edge group and its coset by an
edge reversal. This is the extra group needed to retain edge-conjugation
relations; the vertex/local binary amalgam alone is insufficient.

An isomorphism on the third group, compatible with a similarity, gives inverse
maps on the whole rank-three amalgam. A lift of these inverse maps then gives
exactly the extension required by the recognition theorem.

Source: Aschbacher, *Sporadic Groups* (1994), §§36–37, especially 37.2 and 37.6.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem

universe u v u' v' w
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

namespace System
variable (U : System G V)

/-- A pointwise edge fixer also stabilizes the unordered edge. -/
theorem edgeGroup_le_edgeSetGroup : U.edgeGroup ≤ U.edgeSetGroup :=
  fun _ h => Or.inl h

/-- An element fixing one end and stabilizing the edge fixes both ends. -/
theorem mem_edgeGroup_of_vertex_of_edgeSet {g : G}
    (hx : g ∈ U.vertexGroup) (he : g ∈ U.edgeSetGroup) : g ∈ U.edgeGroup := by
  rcases he with hf | hs
  · exact hf
  · exact False.elim (U.adjacent.ne (hx.symm.trans hs.1))

/-- The intersection of the vertex and setwise-edge groups is the pointwise fixer. -/
theorem vertexGroup_inf_edgeSetGroup :
    U.vertexGroup ⊓ U.edgeSetGroup = U.edgeGroup := by
  apply le_antisymm
  · exact fun _ h => U.mem_edgeGroup_of_vertex_of_edgeSet h.1 h.2
  · exact fun _ h => ⟨h.1, U.edgeGroup_le_edgeSetGroup h⟩

/-- The edge stabilizer has two cosets of the pointwise fixer, represented by an
edge reversal. No assumption that the reversal is an involution is required. -/
theorem edgeSetGroup_cases (t : G) (htx : t • U.x = U.y) (hty : t • U.y = U.x)
    {g : G} (hg : g ∈ U.edgeSetGroup) :
    g ∈ U.edgeGroup ∨ g * t⁻¹ ∈ U.edgeGroup := by
  rcases hg with hf | hs
  · exact Or.inl hf
  · right
    have htx' : t⁻¹ • U.x = U.y := by rw [inv_smul_eq_iff, hty]
    have hty' : t⁻¹ • U.y = U.x := by rw [inv_smul_eq_iff, htx]
    exact ⟨by change (g * t⁻¹) • U.x = U.x; rw [mul_smul, htx', hs.2],
      by change (g * t⁻¹) • U.y = U.y; rw [mul_smul, hty', hs.1]⟩

/-- The edge fixer and the local edge stabilizer generate the full edge stabilizer. -/
theorem edgeSetGroup_generate :
    U.edgeGroup ⊔ (U.H ⊓ U.edgeSetGroup) = U.edgeSetGroup := by
  apply le_antisymm (sup_le U.edgeGroup_le_edgeSetGroup inf_le_right)
  obtain ⟨t, htx, hty⟩ := U.exists_swap
  intro g hg
  rcases U.edgeSetGroup_cases t htx hty hg with h | h
  · exact Subgroup.mem_sup_left h
  · have ht : (t : G) ∈ U.edgeGroup ⊔ (U.H ⊓ U.edgeSetGroup) :=
      Subgroup.mem_sup_right ⟨t.property, Or.inr ⟨htx, hty⟩⟩
    simpa only [inv_mul_cancel_right] using
      (U.edgeGroup ⊔ (U.H ⊓ U.edgeSetGroup)).mul_mem (Subgroup.mem_sup_left h) ht

/-- A compatible map on the genuine rank-three amalgam. -/
structure AmalgamMap (K : Type w) [Group K] where
  vertexHom : U.vertexGroup →* K
  edgeHom : U.edgeSetGroup →* K
  localHom : U.H →* K
  vertex_edge : ∀ (g : G) (hx : g ∈ U.vertexGroup) (he : g ∈ U.edgeSetGroup),
    vertexHom ⟨g, hx⟩ = edgeHom ⟨g, he⟩
  local_vertex : ∀ (g : G) (hH : g ∈ U.H) (hx : g ∈ U.vertexGroup),
    localHom ⟨g, hH⟩ = vertexHom ⟨g, hx⟩
  local_edge : ∀ (g : G) (hH : g ∈ U.H) (he : g ∈ U.edgeSetGroup),
    localHom ⟨g, hH⟩ = edgeHom ⟨g, he⟩

namespace AmalgamMap
variable {U} {K : Type w} [Group K] (m : U.AmalgamMap K)

/-- A lift of compatible amalgam maps to the acting group. -/
structure Lift where
  hom : G →* K
  onVertex : ∀ a : U.vertexGroup, hom a = m.vertexHom a
  onEdge : ∀ a : U.edgeSetGroup, hom a = m.edgeHom a
  onLocal : ∀ a : U.H, hom a = m.localHom a

/-- Generation makes such a lift unique. Existence is the cycle-base theorem. -/
theorem Lift.hom_unique (f g : m.Lift) : f.hom = g.hom := by
  apply U.hom_ext
  · intro a
    exact (f.onLocal a).trans (g.onLocal a).symm
  · intro a
    exact (f.onVertex a).trans (g.onVertex a).symm

end AmalgamMap
end System

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

/-- Extending a similarity to the third group of its rank-three amalgam.
The construction of this local isomorphism uses edge-conjugation compatibility. -/
structure AmalgamEquiv where
  edgeSetIso : U.edgeSetGroup ≃* U'.edgeSetGroup
  onEdge : ∀ b : U.edgeGroup,
    (edgeSetIso ⟨b, U.edgeGroup_le_edgeSetGroup b.property⟩ : G') =
      (s.vertexIso ⟨b, b.property.1⟩ : G')
  onLocal : ∀ (h : U.H) (he : (h : G) ∈ U.edgeSetGroup),
    (edgeSetIso ⟨h, he⟩ : G') = (s.localIso h : G')

namespace AmalgamEquiv
variable {s} (e : s.AmalgamEquiv)

/-- Inverses of the three local isomorphisms form compatible maps into the source. -/
def inverseMap : U'.AmalgamMap G where
  vertexHom := U.vertexGroup.subtype.comp s.vertexIso.symm.toMonoidHom
  edgeHom := U.edgeSetGroup.subtype.comp e.edgeSetIso.symm.toMonoidHom
  localHom := U.H.subtype.comp s.localIso.symm.toMonoidHom
  vertex_edge g hx he := by
    change (s.vertexIso.symm ⟨g, hx⟩ : G) = (e.edgeSetIso.symm ⟨g, he⟩ : G)
    let a : U.vertexGroup := s.vertexIso.symm ⟨g, hx⟩
    have ha : (a : G) ∈ U.edgeGroup := (s.edge a).mpr (by
      simpa only [a, MulEquiv.apply_symm_apply] using
        U'.mem_edgeGroup_of_vertex_of_edgeSet hx he)
    have hi : e.edgeSetIso ⟨a, U.edgeGroup_le_edgeSetGroup ha⟩ = ⟨g, he⟩ := by
      apply Subtype.ext
      exact (e.onEdge ⟨a, ha⟩).trans
        (congrArg (fun b : U'.vertexGroup => (b : G')) (s.vertexIso.apply_symm_apply ⟨g, hx⟩))
    exact congrArg (fun b : U.edgeSetGroup => (b : G))
      ((e.edgeSetIso.symm_apply_apply _).symm.trans (congrArg e.edgeSetIso.symm hi))
  local_vertex g hH hx := by
    change (s.localIso.symm ⟨g, hH⟩ : G) = (s.vertexIso.symm ⟨g, hx⟩ : G)
    let h : U.H := s.localIso.symm ⟨g, hH⟩
    have hh : (h : G) ∈ U.vertexGroup := (s.local_vertex h).mpr (by
      simpa only [h, MulEquiv.apply_symm_apply] using hx)
    have hi : s.vertexIso ⟨h, hh⟩ = ⟨g, hx⟩ := by
      apply Subtype.ext
      exact (s.agree h h.property hh).trans
        (congrArg (fun b : U'.H => (b : G')) (s.localIso.apply_symm_apply ⟨g, hH⟩))
    exact congrArg (fun a : U.vertexGroup => (a : G))
      ((s.vertexIso.symm_apply_apply _).symm.trans (congrArg s.vertexIso.symm hi))
  local_edge g hH he := by
    change (s.localIso.symm ⟨g, hH⟩ : G) = (e.edgeSetIso.symm ⟨g, he⟩ : G)
    let h : U.H := s.localIso.symm ⟨g, hH⟩
    have hh : (h : G) ∈ U.edgeSetGroup := (s.local_edge h).mpr (by
      simpa only [h, MulEquiv.apply_symm_apply] using he)
    have hi : e.edgeSetIso ⟨h, hh⟩ = ⟨g, he⟩ := by
      apply Subtype.ext
      simpa only [h, MulEquiv.apply_symm_apply] using e.onLocal h hh
    exact congrArg (fun a : U.edgeSetGroup => (a : G))
      ((e.edgeSetIso.symm_apply_apply _).symm.trans (congrArg e.edgeSetIso.symm hi))

/-- A lift on the target gives the desired extension into the source.
Only the target will need to satisfy the cycle-base hypothesis. -/
def extensionOfLift (f : e.inverseMap.Lift) : s.Extension where
  hom := f.hom
  onVertex a := by simpa [inverseMap] using f.onVertex (s.vertexIso a)
  onLocal a := by simpa [inverseMap] using f.onLocal (s.localIso a)

end AmalgamEquiv
end Similarity
end Theory.GroupTheory.GraphUniquenessSystem
