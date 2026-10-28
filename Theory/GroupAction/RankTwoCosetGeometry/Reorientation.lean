module
public import Theory.GroupAction.RankTwoCosetGeometry

/-!
# Reversing the two vertex types of the same coset action

Exchanging the two local subgroups only changes the type labels. The literal
cosets give an equivariant graph isomorphism, preserving the original acting
group and exchanging the two base vertices. This handles both orientations
of the first singular arc in Goldschmidt (1980), Sections 5--6.
-/

@[expose] public section
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

def swapFamily : Bool → Subgroup G := fun i => F (!i)

def swapVertex : Vertex F → Vertex (swapFamily F)
  | ⟨false,q⟩ => ⟨true,q⟩
  | ⟨true,q⟩ => ⟨false,q⟩

def swapVertexEquiv : Vertex F ≃ Vertex (swapFamily F) where
  toFun := swapVertex F
  invFun
    | ⟨false,q⟩ => ⟨true,q⟩
    | ⟨true,q⟩ => ⟨false,q⟩
  left_inv v := by rcases v with ⟨i,q⟩; cases i <;> rfl
  right_inv v := by rcases v with ⟨i,q⟩; cases i <;> rfl

@[simp] theorem swapVertex_type (v : Vertex F) : (swapVertex F v).type = !v.type := by
  rcases v with ⟨i,q⟩; cases i <;> rfl

@[simp] theorem swapVertex_smul (g : G) (v : Vertex F) :
    swapVertex F (g • v) = g • swapVertex F v := by
  rcases v with ⟨i,q⟩; cases i <;> rfl

@[simp] theorem swapVertex_base (i : Bool) :
    swapVertex F (base F i) = base (swapFamily F) (!i) := by cases i <;> rfl

def swapGraphIso : graph F ≃g graph (swapFamily F) where
  toEquiv := swapVertexEquiv F
  map_rel_iff' := by
    rintro ⟨i,q⟩ ⟨j,r⟩
    cases i <;> cases j <;>
      simp [incidenceGraph_adj, swapVertexEquiv, swapVertex, swapFamily, Incident] <;> rfl

end Subgroup.CosetGeometry.RankTwo

