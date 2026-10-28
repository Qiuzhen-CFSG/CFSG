module
public import Theory.GroupTheory.CubicAutomorphismLines

/-!
# Independent inversions on two cubic directions

Restrict a faithful action to two invariant cubic subgroups generating
an abelian group. The two restrictions embed the actor into C₂ × C₂.
If the actor has at least four elements, this embedding is onto, giving
an element fixing the first direction and inverting the second.
The usual cubic projection argument excludes any third invariant line.

Source: the action calculation in Aschbacher--Smith 15.2.23 (*),
printed p.1116. The application retains the original Sylow action;
a single diagonal inverter would not satisfy the cardinal hypothesis.
-/

public section
open Subgroup
namespace Theory.GroupTheory.CubicAutomorphismLines
variable {D Q : Type*} [Group D] [CommGroup Q] [Finite Q]

private def restriction (ρ : D →* MulAut Q) (A : Subgroup Q)
    (hA : ∀ d : D, ∀ x ∈ A, ρ d x ∈ A) : D →* MulAut A where
  toFun d :=
    { toFun x := ⟨ρ d (x : Q), hA d (x : Q) x.property⟩
      invFun x := ⟨ρ d⁻¹ (x : Q), hA d⁻¹ (x : Q) x.property⟩
      left_inv x := by
        apply Subtype.ext
        change ρ d⁻¹ (ρ d (x : Q)) = (x : Q)
        rw [← MulAut.mul_apply,← map_mul,inv_mul_cancel,map_one]
        rfl
      right_inv x := by
        apply Subtype.ext
        change ρ d (ρ d⁻¹ (x : Q)) = (x : Q)
        rw [← MulAut.mul_apply,← map_mul,mul_inv_cancel,map_one]
        rfl
      map_mul' x y := by apply Subtype.ext; exact map_mul (ρ d) (x : Q) (y : Q) }
  map_one' := by ext x; exact congrArg (fun a : MulAut Q => a x) ρ.map_one
  map_mul' d e := by ext x; exact congrArg (fun a : MulAut Q => a x) (ρ.map_mul d e)

private def inversion (A : Subgroup Q) : MulAut A where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' x y := by rw [mul_inv_rev,mul_comm]

/-- A faithful action of order at least four preserving two complementary
cubic lines contains an actor fixing the first and inverting the second. -/
theorem exists_independent_inversion (ρ : D →* MulAut Q)
    (hi : Function.Injective ρ) (hD : 4 ≤ Nat.card D)
    (A B : Subgroup Q) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hgen : A ⊔ B = ⊤)
    (ha : ∀ d : D, ∀ x ∈ A, ρ d x ∈ A)
    (hb : ∀ d : D, ∀ x ∈ B, ρ d x ∈ B) :
    ∃ d : D, (∀ x ∈ A, ρ d x = x) ∧ (∀ x ∈ B, ρ d x = x⁻¹) := by
  let r := (restriction ρ A ha).prod (restriction ρ B hb)
  have hr : Function.Injective r := by
    intro d e hde
    apply hi
    apply MulEquiv.ext
    intro x
    have hx : x ∈ A ⊔ B := hgen.symm ▸ mem_top x
    obtain ⟨a,ha',b,hb',he⟩ := mem_sup_of_normal_right.mp hx
    rw [← he,map_mul,map_mul]
    have h1 := congrArg (fun z : MulAut A × MulAut B => (z.1 ⟨a,ha'⟩ : Q)) hde
    have h2 := congrArg (fun z : MulAut A × MulAut B => (z.2 ⟨b,hb'⟩ : Q)) hde
    exact congrArg₂ (· * ·) h1 h2
  have hc : Nat.card (MulAut A × MulAut B) = 4 := by
    let : IsCyclic A := isCyclic_of_prime_card hA
    let : IsCyclic B := isCyclic_of_prime_card hB
    rw [Nat.card_prod,IsCyclic.card_mulAut,IsCyclic.card_mulAut,hA,hB]
    decide
  have hs : Function.Surjective r := by
    apply ((Nat.bijective_iff_injective_and_card r).mpr ⟨hr, ?_⟩).2
    exact (le_antisymm (Nat.card_le_card_of_injective r hr) (hc ▸ hD))
  obtain ⟨d,hd⟩ := hs (1,inversion B)
  refine ⟨d,?_,?_⟩
  · intro x hx
    exact congrArg (fun z : MulAut A × MulAut B => (z.1 ⟨x,hx⟩ : Q)) hd
  · intro x hx
    exact congrArg (fun z : MulAut A × MulAut B => (z.2 ⟨x,hx⟩ : Q)) hd

/-- Independent inversion rules out a third invariant cubic direction. -/
theorem invariant_eq_of_four_actors (ρ : D →* MulAut Q)
    (hi : Function.Injective ρ) (hD : 4 ≤ Nat.card D)
    (A B C : Subgroup Q) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hC : Nat.card C = 3) (hgen : A ⊔ B = ⊤)
    (ha : ∀ d : D, ∀ x ∈ A, ρ d x ∈ A)
    (hb : ∀ d : D, ∀ x ∈ B, ρ d x ∈ B)
    (hc : ∀ d : D, ∀ x ∈ C, ρ d x ∈ C) : C = A ∨ C = B := by
  obtain ⟨d,hfix,hinv⟩ := exists_independent_inversion ρ hi hD A B hA hB hgen ha hb
  exact invariant_line_eq A B C hA hB hC hgen (ρ d) hfix hinv (hc d)

end Theory.GroupTheory.CubicAutomorphismLines
