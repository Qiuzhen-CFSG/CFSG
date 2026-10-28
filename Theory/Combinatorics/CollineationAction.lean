module

public import Theory.Combinatorics.FullCollineation
public import Theory.Combinatorics.ProjectivePlaneCollineation

/-!
# Transport and faithful actions of incidence collineations

An incidence identification conjugates the full collineation groups by its
point and line equivalences. An incidence-preserving group action gives a
homomorphism into the full collineation group, injective whenever the line
action is faithful. Neither construction requires projective-plane axioms.
-/

namespace Configuration.Collineation

variable {P L P' L' : Type*} [Membership P L] [Membership P' L']

/-- Transport collineations along an incidence-preserving pair of equivalences. -/
@[expose] public def transport (ep : P ≃ P') (el : L ≃ L')
    (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) : Collineation P L →* Collineation P' L' where
  toFun c := ⟨(ep.permCongrHom (pointHom P L c), el.permCongrHom (lineHom P L c)), by
    intro p l
    change ep (pointHom P L c (ep.symm p)) ∈ el (lineHom P L c (el.symm l)) ↔ p ∈ l
    rw [hi, mem_iff]
    simpa using (hi (ep.symm p) (el.symm l)).symm⟩
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (by simp only [map_one]; rfl) (by simp only [map_one]; rfl)
  map_mul' a b := by
    apply Subtype.ext
    exact Prod.ext (by simp) (by simp)

@[simp] public theorem transport_point (ep : P ≃ P') (el : L ≃ L')
    (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) (c : Collineation P L) (p : P') :
    pointHom P' L' (transport ep el hi c) p = ep (pointHom P L c (ep.symm p)) := rfl

@[simp] public theorem transport_line (ep : P ≃ P') (el : L ≃ L')
    (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) (c : Collineation P L) (l : L') :
    lineHom P' L' (transport ep el hi c) l = el (lineHom P L c (el.symm l)) := rfl

/-- Incidence identification induces an equivalence of full collineation groups. -/
@[expose] public def congr (ep : P ≃ P') (el : L ≃ L')
    (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) : Collineation P L ≃* Collineation P' L' where
  toFun := transport ep el hi
  invFun := transport ep.symm el.symm (fun p l => by
    simpa using (hi (ep.symm p) (el.symm l)).symm)
  left_inv c := by apply ext <;> intro x <;> simp
  right_inv c := by apply ext <;> intro x <;> simp
  map_mul' := (transport ep el hi).map_mul

@[simp] public theorem congr_apply (ep : P ≃ P') (el : L ≃ L')
    (hi : ∀ p l, ep p ∈ el l ↔ p ∈ l) (c : Collineation P L) :
    congr ep el hi c = transport ep el hi c := rfl

variable (G P L : Type*) [Group G] [Membership P L]
  [MulAction G P] [MulAction G L] [IsCollineationAction G P L]

/-- An incidence-preserving action as a homomorphism to the full collineation group. -/
@[expose] public def ofAction : G →* Collineation P L where
  toFun g := ⟨(MulAction.toPermHom G P g, MulAction.toPermHom G L g),
    IsCollineationAction.smul_mem_smul_iff g⟩
  map_one' := by apply Subtype.ext; exact Prod.ext (map_one _) (map_one _)
  map_mul' g h := by apply Subtype.ext; exact Prod.ext (map_mul _ g h) (map_mul _ g h)

@[simp] public theorem ofAction_point (g : G) (p : P) :
    pointHom P L (ofAction G P L g) p = g • p := rfl

@[simp] public theorem ofAction_line (g : G) (l : L) :
    lineHom P L (ofAction G P L g) l = g • l := rfl

/-- Faithfulness on lines makes the incidence action an embedding. -/
public theorem ofAction_injective [FaithfulSMul G L] :
    Function.Injective (ofAction G P L) := by
  intro g h heq
  apply eq_of_smul_eq_smul (α := L)
  intro l
  exact congrArg (fun c => lineHom P L c l) heq

end Configuration.Collineation
