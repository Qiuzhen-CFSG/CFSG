module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Edges.Reduction

/-!
# Witness-action certificates for Fi23 exhaustion edges

A checked action table denotes an actual element of the closure of the eight
unchanged witness permutations. Products and inverses retain this property.
An edge is certified by comparing `letter * representative` with
`nextRepresentative * witnessWord` at every original coordinate. This avoids
numerically evaluating an inverse representative, and keeps every equality
in the literal permutation action on 31671 points.

Source: ATLAS F23G1-p31671B0, GLS3 Table 5.3u. The residual A and B families
consume this interface; the final edge assembly remains in `Edges.lean`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
open Fi24Prime.Fi23Lift.Certificate

/-- A packed map uses the same block size and bit width as the source maps. -/
def tableAction (table : Nat → Nat) (x : Fin 31671) : Fin 31671 :=
  ⟨lookup table 15 x.val % 31671, Nat.mod_lt _ (by decide)⟩

/-- Both directions of an action, together with genuine subgroup membership. -/
structure Entry where
  forward : Nat → Nat
  backward : Nat → Nat
  valid : ∃ p : Equiv.Perm (Fin 31671), p ∈ witnessGroup ∧
    (∀ x, tableAction forward x = p x) ∧
    (∀ x, tableAction backward x = p⁻¹ x)

noncomputable def Entry.element (e : Entry) : Equiv.Perm (Fin 31671) := e.valid.choose

theorem Entry.element_mem (e : Entry) : e.element ∈ witnessGroup := e.valid.choose_spec.1

def Entry.action (e : Entry) (inverse : Bool) (x : Fin 31671) : Fin 31671 :=
  tableAction (if inverse then e.backward else e.forward) x

theorem Entry.action_eq (e : Entry) (inverse : Bool) (x : Fin 31671) :
    e.action inverse x = (if inverse then e.element⁻¹ else e.element) x := by
  cases inverse
  · exact e.valid.choose_spec.2.1 x
  · exact e.valid.choose_spec.2.2 x

noncomputable def productElement (w : List (Entry × Bool)) : Equiv.Perm (Fin 31671) :=
  (w.map (fun eb => if eb.2 then eb.1.element⁻¹ else eb.1.element)).prod

def productAction (w : List (Entry × Bool)) (x : Fin 31671) : Fin 31671 :=
  w.foldr (fun eb y => eb.1.action eb.2 y) x

theorem productElement_mem (w : List (Entry × Bool)) : productElement w ∈ witnessGroup := by
  apply Subgroup.list_prod_mem
  intro p hp
  obtain ⟨⟨e, b⟩, _, rfl⟩ := List.mem_map.mp hp
  cases b
  · exact e.element_mem
  · exact witnessGroup.inv_mem e.element_mem

theorem productAction_eq (w : List (Entry × Bool)) (x : Fin 31671) :
    productAction w x = productElement w x := by
  induction w with
  | nil => rfl
  | cons eb w ih =>
    simpa only [productAction, productElement, List.foldr_cons, List.map_cons,
      List.prod_cons, Equiv.Perm.mul_apply, Entry.action_eq] using
        congrArg (fun y => (if eb.2 then eb.1.element⁻¹ else eb.1.element) y) ih

/-- Certify a table and its inverse using one known subgroup element. -/
def ofElement (forward backward : Nat → Nat) (p : Equiv.Perm (Fin 31671))
    (hp : p ∈ witnessGroup)
    (hf : ∀ x, tableAction forward x = p x)
    (hi : ∀ x, tableAction forward (tableAction backward x) = x) : Entry :=
  ⟨forward, backward, p, hp, hf, fun x => by
    apply p.injective
    rw [← hf, hi]
    exact (p.apply_symm_apply x).symm⟩

/-- Initial entries must certify the original witness generators. -/
def ofGenerator (j : Fin 8) (forward backward : Nat → Nat)
    (hf : ∀ x, tableAction forward x = witnessGenerator j x)
    (hi : ∀ x, tableAction forward (tableAction backward x) = x) : Entry :=
  ofElement forward backward (witnessGenerator j)
    (Subgroup.subset_closure ⟨j, rfl⟩) hf hi

/-- Share a certified product instead of reevaluating a long witness word. -/
noncomputable def ofProduct (w : List (Entry × Bool)) (forward backward : Nat → Nat)
    (hf : ∀ x, tableAction forward x = productAction w x)
    (hi : ∀ x, tableAction forward (tableAction backward x) = x) : Entry :=
  ofElement forward backward (productElement w) (productElement_mem w)
    (fun x => (hf x).trans (productAction_eq w x)) hi

/-- Every coordinate is checked; the extra 1097 indices in a 2^15 block are padding. -/
def actionCheck (f g : Fin 31671 → Fin 31671) (n : Nat) : Bool :=
  if hn : n < 31671 then decide (f ⟨n, hn⟩ = g ⟨n, hn⟩) else true

theorem actionCheck_sound (f g : Fin 31671 → Fin 31671)
    (h : checkPow (actionCheck f g) 0 15 = true) : ∀ x, f x = g x := by
  intro x
  have hx := checkPow_sound _ 15 0 h x.val (Nat.zero_le _)
    (Nat.lt_trans x.isLt (by decide))
  simpa only [actionCheck, dif_pos x.isLt, decide_eq_true_eq] using hx

private theorem cancel_edge {α : Type*} (r s t p : Equiv.Perm α)
    (h : ∀ x, s (t x) = r (p x)) : r⁻¹ * s * t = p := by
  have he : s * t = r * p := Equiv.ext h
  calc
    _ = r⁻¹ * (s * t) := mul_assoc _ _ _
    _ = p := by rw [he, inv_mul_cancel_left]

/-- Numerical equality with a certified word proves the literal edge membership. -/
theorem edge_mem_of_product_action
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)
    (b : Bool) (x : Fin 31671) (w : List (Entry × Bool))
    (h : ∀ y, packedLetter b (representativeAction x y) =
      representativeAction (packedLetter b x) (productAction w y)) :
    inclusion (edge b x) ∈ witnessGroup := by
  have he : inclusion (edge b x) = productElement w := by
    simp only [edge, map_mul, map_inv]
    apply cancel_edge
    intro y
    simpa only [packedLetter_eq hA hB, representativeAction_eq hA hB,
      productAction_eq] using h y
  rw [he]
  exact productElement_mem w

/-- The residual certificate producers can discharge the pointwise equality by
bounded, kernel-checked blocks and `checkPow_join`. -/
theorem edge_mem_of_product_check
    (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)
    (b : Bool) (x : Fin 31671) (w : List (Entry × Bool))
    (h : checkPow (actionCheck
      (fun y => packedLetter b (representativeAction x y))
      (fun y => representativeAction (packedLetter b x) (productAction w y))) 0 15 = true) :
    inclusion (edge b x) ∈ witnessGroup :=
  edge_mem_of_product_action hA hB b x w (actionCheck_sound _ _ h)

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
