module
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Schreier elements for coset-word certificates

Along any proposed transition table, the elements
`ρ i * g a * (ρ j)⁻¹` telescope. A relator loop therefore supplies an
actual equation in these elements, without assuming that they belong to a
particular subgroup. Proving their subgroup membership then supplies `Holds`.

This is the elementary telescoping step of Schreier rewriting. It extends the
coset-word certificate semantics; no faithfulness or finiteness is required.
-/

@[expose] public section
namespace Subgroup.CosetWordCertificate
variable {G α : Type*} [Group G]
/-- The Schreier element attached to a signed edge. -/
def edgeElement (ρ : Nat → G) (g : α → G) (i : Nat) (a : Letter α) (j : Nat) : G :=
  ρ i * eval g [a] * (ρ j)⁻¹

theorem holds_iff_schreier_mem (H : Subgroup G) (g : α → G) (ρ : Nat → G)
    (f : FactData α) : Holds H g ρ f ↔ ρ f.left * eval g f.word * (ρ f.right)⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh⟩
    rw [hh, mul_inv_cancel_right]
    exact h.property
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    simp [mul_assoc]

/-- Following a candidate table determines actual Schreier factors, independently
of whether those factors belong to the intended subgroup. -/
def traceEnd (next : Nat → Letter α → Nat) (i : Nat) : Word α → Nat
  | [] => i
  | a :: w => traceEnd next (next i a) w

def traceElements (next : Nat → Letter α → Nat) (ρ : Nat → G) (g : α → G)
    (i : Nat) : Word α → List G
  | [] => []
  | a :: w => edgeElement ρ g i a (next i a) :: traceElements next ρ g (next i a) w

theorem traceElements_prod (next : Nat → Letter α → Nat) (ρ : Nat → G)
    (g : α → G) (i : Nat) (w : Word α) :
    (traceElements next ρ g i w).prod = ρ i * eval g w * (ρ (traceEnd next i w))⁻¹ := by
  induction w generalizing i with
  | nil => simp [traceElements, traceEnd]
  | cons a w ih =>
    simp only [traceElements, List.prod_cons, ih, traceEnd, edgeElement]
    rw [show eval g (a :: w) = eval g [a] * eval g w from eval_append g [a] w]
    simp [mul_assoc]

/-- Each retained relator supplies an honest equation in the edge elements. -/
theorem traceElements_relator (next : Nat → Letter α → Nat) (ρ : Nat → G)
    (g : α → G) (i : Nat) (w : Word α) (hw : eval g w = 1)
    (hloop : traceEnd next i w = i) : (traceElements next ρ g i w).prod = 1 := by
  rw [traceElements_prod, hw, hloop]
  simp

/-- Words in subgroup elements remain in the subgroup, including inverse letters. -/
theorem eval_mem_of_generators_mem (H : Subgroup G) (g : α → G)
    (hg : ∀ a, g a ∈ H) (w : Word α) : eval g w ∈ H := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply H.mul_mem _ ih
    split
    · exact hg _
    · exact H.inv_mem (hg _)
end Subgroup.CosetWordCertificate
