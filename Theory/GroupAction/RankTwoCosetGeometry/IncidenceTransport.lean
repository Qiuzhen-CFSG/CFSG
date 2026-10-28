module

public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane

/-!
# Transport between the two fibers of coset incidence graphs

A pair of incidence-preserving equivalences on points and lines combines into
a type-preserving graph isomorphism. Equivariance of the two maps gives
equivariance of this graph isomorphism for the same group homomorphism.
The construction retains false as the point type and true as the line type.

This elementary transport is used when identifying a rank-two completion's
plane with the model plane in Aschbacher–Smith F.4.8(2), p.278.
-/

public section

namespace Subgroup.CosetGeometry.RankTwo
noncomputable section
variable {G H : Type*} [Group G] [Group H]
variable (F : Bool → Subgroup G) (E : Bool → Subgroup H)

private def vertexEquivFibers : Vertex F ≃ Point F ⊕ Line F where
  toFun
    | ⟨false, q⟩ => Sum.inl ⟨⟨false, q⟩, rfl⟩
    | ⟨true, q⟩ => Sum.inr ⟨⟨true, q⟩, rfl⟩
  invFun
    | Sum.inl p => p.val
    | Sum.inr l => l.val
  left_inv v := by rcases v with ⟨i, v⟩; cases i <;> rfl
  right_inv v := by
    rcases v with ⟨⟨i, q⟩, h⟩ | ⟨⟨i, q⟩, h⟩ <;> dsimp only at h <;> subst i <;> rfl

variable (ep : Point F ≃ Point E) (el : Line F ≃ Line E)
  (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l)

def graphIsoOfIncidence : graph F ≃g graph E where
  toEquiv := (vertexEquivFibers F).trans ((Equiv.sumCongr ep el).trans
    (vertexEquivFibers E).symm)
  map_rel_iff' := by
    intro v w
    rcases v with ⟨i, v⟩
    rcases w with ⟨j, w⟩
    cases i <;> cases j
    · change (((ep ⟨⟨false, v⟩, rfl⟩).val.type ≠ (ep ⟨⟨false, w⟩, rfl⟩).val.type) ∧ _) ↔
        ((false ≠ false) ∧ _)
      simp only [(ep _).property, ne_self_iff_false, false_and]
    · exact hi ⟨⟨false, v⟩, rfl⟩ ⟨⟨true, w⟩, rfl⟩
    · change (graph E).Adj (el ⟨⟨true, v⟩, rfl⟩).val (ep ⟨⟨false, w⟩, rfl⟩).val ↔
        (graph F).Adj ⟨true, v⟩ ⟨false, w⟩
      rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := graph F)]
      exact hi ⟨⟨false, w⟩, rfl⟩ ⟨⟨true, v⟩, rfl⟩
    · change (((el ⟨⟨true, v⟩, rfl⟩).val.type ≠ (el ⟨⟨true, w⟩, rfl⟩).val.type) ∧ _) ↔
        ((true ≠ true) ∧ _)
      simp only [(el _).property, ne_self_iff_false, false_and]

@[simp] theorem graphIsoOfIncidence_point (p : Point F) :
    graphIsoOfIncidence F E ep el hi p.val = (ep p).val := by
  rcases p with ⟨⟨i, p⟩, h⟩
  dsimp only at h
  subst i
  rfl

@[simp] theorem graphIsoOfIncidence_line (l : Line F) :
    graphIsoOfIncidence F E ep el hi l.val = (el l).val := by
  rcases l with ⟨⟨i, l⟩, h⟩
  dsimp only at h
  subst i
  rfl

theorem graphIsoOfIncidence_type (v : Vertex F) :
    (graphIsoOfIncidence F E ep el hi v).type = v.type := by
  cases h : v.type
  · have he := graphIsoOfIncidence_point F E ep el hi ⟨v, h⟩
    rw [he]
    exact (ep ⟨v, h⟩).property
  · have he := graphIsoOfIncidence_line F E ep el hi ⟨v, h⟩
    rw [he]
    exact (el ⟨v, h⟩).property

theorem graphIsoOfIncidence_equivariant (f : G →* H)
    (hp : ∀ g p, ep (g • p) = f g • ep p)
    (hl : ∀ g l, el (g • l) = f g • el l) (g : G) (v : Vertex F) :
    graphIsoOfIncidence F E ep el hi (g • v) = f g • graphIsoOfIncidence F E ep el hi v := by
  cases h : v.type
  · have h₁ := graphIsoOfIncidence_point F E ep el hi (g • (⟨v, h⟩ : Point F))
    have h₂ := graphIsoOfIncidence_point F E ep el hi (⟨v, h⟩ : Point F)
    exact h₁.trans ((congrArg Subtype.val (hp g ⟨v, h⟩)).trans (congrArg (f g • ·) h₂.symm))
  · have h₁ := graphIsoOfIncidence_line F E ep el hi (g • (⟨v, h⟩ : Line F))
    have h₂ := graphIsoOfIncidence_line F E ep el hi (⟨v, h⟩ : Line F)
    exact h₁.trans ((congrArg Subtype.val (hl g ⟨v, h⟩)).trans (congrArg (f g • ·) h₂.symm))
end
end Subgroup.CosetGeometry.RankTwo
