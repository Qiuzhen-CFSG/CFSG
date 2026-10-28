module
public import Theory.Combinatorics.DuadGraph.Stars
/-!
# Faithful six-point action of disjoint-duad graph automorphisms

Every graph automorphism permutes the independent five-sets. The structural
classification identifies those sets with the six point stars. Transporting
this permutation action gives pointAction. Incidence with the stars recovers
each duad, so the action is faithful. The incidence theorem retains the
literal vertex permutation, ready for transporting an original graph action.

Source application: the SRG(15,6,1,3) action in U₄(3) recognition.
-/

@[expose] public section
namespace Theory.Combinatorics.DuadGraph
open Finset
abbrev Five := {F : Finset Vertex // graph.IsNIndepSet 5 F}

def mapFive (g : Aut) (F : Five) : Five := ⟨F.val.image g, by
  constructor
  · intro s hs t ht hne hadj
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hs
    obtain ⟨y,hy,rfl⟩ := mem_image.mp ht
    exact F.property.isIndepSet hx hy (fun he => hne (congrArg g he)) (g.map_adj_iff.mp hadj)
  · rw [card_image_of_injective _ g.injective,F.property.card_eq]⟩

@[simp] theorem mapFive_one (F : Five) : mapFive 1 F=F := by
  apply Subtype.ext
  simp [mapFive]

@[simp] theorem mapFive_mul (g h : Aut) (F : Five) : mapFive (g*h) F=mapFive g (mapFive h F) := by
  apply Subtype.ext
  simp [mapFive,Finset.image_image,Function.comp_def]

def fivePerm (g : Aut) : Equiv.Perm Five where
  toFun := mapFive g
  invFun := mapFive g⁻¹
  left_inv F := by rw [←mapFive_mul,inv_mul_cancel,mapFive_one]
  right_inv F := by rw [←mapFive_mul,mul_inv_cancel,mapFive_one]

noncomputable def pointPerm (g : Aut) : Equiv.Perm (Fin 6) :=
  starEquiv.trans ((fivePerm g).trans starEquiv.symm)

@[simp] theorem pointPerm_apply (g : Aut) (a : Fin 6) :
    pointPerm g a=starEquiv.symm (mapFive g (starEquiv a)) := rfl

noncomputable def pointAction : Aut →* Equiv.Perm (Fin 6) where
  toFun := pointPerm
  map_one' := by
    ext a
    simp [pointPerm_apply]
  map_mul' g h := by
    ext a
    simp [pointPerm_apply,Equiv.Perm.mul_apply]

/-- The six-letter action is the actual action on point stars. -/
theorem pointAction_star (g : Aut) (a : Fin 6) :
    star (pointAction g a)=(star a).image g := by
  have he := congrArg Subtype.val (starEquiv.apply_symm_apply (mapFive g (starEquiv a)))
  change star (starEquiv.symm (mapFive g (starEquiv a))) = _
  simpa only [starEquiv_val,mapFive] using he

/-- The original incidence between points and duads is preserved. -/
theorem pointAction_mem (g : Aut) (a : Fin 6) (s : Vertex) :
    pointAction g a ∈ (g s).val ↔ a∈s.val := by
  rw [←mem_star,pointAction_star]
  simp only [mem_image,g.injective.eq_iff,exists_eq_right,mem_star]

/-- A permutation of duads fixing each point star fixes every duad. -/
theorem pointAction_injective : Function.Injective pointAction := by
  intro g h he
  apply RelIso.ext
  intro s
  apply Subtype.ext
  ext b
  obtain ⟨a,rfl⟩ := (pointAction g).surjective b
  rw [pointAction_mem,he,pointAction_mem]

end Theory.Combinatorics.DuadGraph
