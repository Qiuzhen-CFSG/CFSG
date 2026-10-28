module

public import Theory.GroupAction.CubicTree.ArcTransport
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card

/-!
# Nonregular arcs are totally singular in valence three

There are precisely two forward choices at a nontrivial arc. An automorphism
fixing the arc permutes these choices; if any such automorphism moves one choice,
the stabilizer is transitive on both. Thus failure of regularity means that every
choice is fixed. Reversal supplies the corresponding left-end assertion.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the definitions
before (2.12), printed p.383, and the remark following (2.12), printed p.384.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

theorem card_forward_of_cubic {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x)
    (hcard : Nat.card (Γ.neighborSet p.endpoint) = 3) :
    Nat.card {z : V // Forward p z} = 2 := by
  classical
  let : Finite (Γ.neighborSet p.endpoint) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Fintype (Γ.neighborSet p.endpoint) := Fintype.ofFinite _
  let e : {z : V // Forward p z} ≃
      {z : Γ.neighborSet p.endpoint // z ≠ ⟨p.penultimate, p.adj_penultimate_endpoint.symm⟩} := {
    toFun z := ⟨⟨z, z.property.1⟩, fun he => z.property.2 (congrArg Subtype.val he)⟩
    invFun z := ⟨z.val, z.val.property, fun he => z.property (Subtype.ext he)⟩
    left_inv z := rfl
    right_inv z := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, hcard]
  simp

private theorem forward_eq_of_vertices_eq {n : ℕ} {x y z : V}
    (p : BasedWalk Γ n x) (q : BasedWalk Γ n y) (he : p.vertices = q.vertices) :
    Forward p z ↔ Forward q z := by
  have hxy : x = y := Option.some.inj (by
    simpa only [BasedWalk.head_vertices] using congrArg List.head? he)
  subst y
  rw [BasedWalk.vertices_injective n x he]

theorem forward_smul_of_fixes (h : GraphAction Γ A) {n : ℕ} {x z : V}
    (p : BasedWalk Γ n x) (a : A) (ha : ∀ y ∈ p.vertices, a • y = y)
    (hz : Forward p z) : Forward p (a • z) := by
  have he : (p.map (h.hom a)).vertices = p.vertices := by
    rw [BasedWalk.vertices_map]
    change p.vertices.map (a • ·) = p.vertices
    simpa only [List.map_id] using
      (List.map_congr_left (f := fun y => a • y) (g := id) ha)
  exact (forward_eq_of_vertices_eq _ _ he).1 ((forward_map_iff h a p).2 hz)

/-- On the two possible extensions, one moved point implies transitivity. -/
theorem rightRegular_of_moved_forward (h : GraphAction Γ A)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x)
    (hcard : Nat.card (Γ.neighborSet p.endpoint) = 3)
    (a : A) (ha : ∀ y ∈ p.vertices, a • y = y)
    {z : V} (hz : Forward p z) (hm : a • z ≠ z) : RightRegular (A := A) p := by
  classical
  have htwo : ({w : V | Forward p w} : Set V).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact card_forward_of_cubic p hcard
  obtain ⟨u, v, huv, he⟩ := Set.ncard_eq_two.mp htwo
  have hcases : ∀ w, Forward p w → w = z ∨ w = a • z := by
    have hz' : z = u ∨ z = v := by
      have hh : z ∈ {w : V | Forward p w} := hz
      simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    have haz' : a • z = u ∨ a • z = v := by
      have hh : a • z ∈ {w : V | Forward p w} := forward_smul_of_fixes h p a ha hz
      simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    intro w hw
    have hw' : w = u ∨ w = v := by
      have hh : w ∈ {t : V | Forward p t} := hw
      simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    aesop
  intro u v hu hv
  rcases hcases u hu with hu | hu <;> rcases hcases v hv with hv | hv
  · exact ⟨1, fun y _ => one_smul A y, by simp only [hu, hv, one_smul]⟩
  · exact ⟨a, ha, by rw [hu, hv]⟩
  · exact ⟨a⁻¹, fun y hy => inv_smul_eq_iff.mpr (ha y hy).symm,
      by simp only [hu, hv, inv_smul_smul]⟩
  · exact ⟨1, fun y _ => one_smul A y, by simp only [hu, hv, one_smul]⟩

theorem fixes_forward_of_not_rightRegular (h : GraphAction Γ A)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x)
    (hcard : Nat.card (Γ.neighborSet p.endpoint) = 3)
    (hn : ¬ RightRegular (A := A) p)
    (a : A) (ha : ∀ y ∈ p.vertices, a • y = y) {z : V} (hz : Forward p z) :
    a • z = z := by
  by_contra hm
  exact hn (rightRegular_of_moved_forward h p hcard a ha hz hm)

theorem fixes_backward_of_not_leftRegular (h : GraphAction Γ A)
    {n : ℕ} {x : V} (p : BasedWalk Γ (n + 1) x)
    (hcard : Nat.card (Γ.neighborSet x) = 3)
    (hn : ¬ LeftRegular (A := A) p)
    (a : A) (ha : ∀ y ∈ p.vertices, a • y = y) {z : V} (hz : Backward p z) :
    a • z = z := by
  apply fixes_forward_of_not_rightRegular h (reverse p)
      (by simpa only [endpoint_reverse] using hcard)
      (fun hr => hn ((rightRegular_reverse_iff p).1 hr)) a
      (by simpa only [vertices_reverse, List.mem_reverse] using ha)
  exact (forward_reverse_iff_backward p).2 hz

end Theory.GroupAction.CubicTree
