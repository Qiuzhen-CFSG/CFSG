module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.SimpleQuotients

/-!
# Quotient alternatives for the flag-module factors

A nonzero simple quotient of the product of a trivial line, two extensions
with reversed simple factors, and a third simple module is one of the four
specified simple modules. Work with abstract module carriers so the proof
can later be specialized to the trace-zero adjoint space without repeatedly
expanding its algebraic instances.

This assembles the factors in the direct proof of Aschbacher–Smith H.6.1
from the concrete H.6.2 flag decomposition, printed pp.386–387.
-/

public section

open Representation
namespace BinaryLinearThree.IrreducibleCatalogue

theorem classify_product_extension_quotient
    {G A B C X Y M : Type*} [Monoid G]
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup C] [Module (ZMod 2) C] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup M] [Module (ZMod 2) M]
    {α : Representation (ZMod 2) G A} {β : Representation (ZMod 2) G B}
    {γ : Representation (ZMod 2) G C} {ξ : Representation (ZMod 2) G X}
    {η : Representation (ZMod 2) G Y} {ρ : Representation (ZMod 2) G M}
    [IsIrreducible α] [IsIrreducible β] [IsIrreducible γ] [IsIrreducible ρ]
    (i₁ : β.IntertwiningMap ξ) (π₁ : ξ.IntertwiningMap α)
    (hπ₁ : Function.Surjective π₁)
    (he₁ : LinearMap.range i₁.toLinearMap = LinearMap.ker π₁.toLinearMap)
    (i₂ : α.IntertwiningMap η) (π₂ : η.IntertwiningMap β)
    (hπ₂ : Function.Surjective π₂)
    (he₂ : LinearMap.range i₂.toLinearMap = LinearMap.ker π₂.toLinearMap)
    (q : ((Representation.trivial (ZMod 2) G (ZMod 2)).prod (ξ.prod (η.prod γ))).IntertwiningMap ρ)
    (hq : q ≠ 0) :
    Nonempty (ρ.Equiv (Representation.trivial (ZMod 2) G (ZMod 2))) ∨
      Nonempty (ρ.Equiv α) ∨ Nonempty (ρ.Equiv β) ∨ Nonempty (ρ.Equiv γ) := by
  rcases nonzero_restriction_of_prod q hq with htriv | hrest
  · exact Or.inl (simple_quotient_of_binary_trivial _ htriv)
  · let q1 := q.comp (IntertwiningMap.inr (ZMod 2)
      (Representation.trivial (ZMod 2) G (ZMod 2)) (ξ.prod (η.prod γ)))
    rcases nonzero_restriction_of_prod q1 hrest with hp | hls
    · rcases simple_quotient_of_extension i₁ π₁ hπ₁ he₁ _ hp with hd | hn
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hn)
    · let q2 := q1.comp (IntertwiningMap.inr (ZMod 2) ξ (η.prod γ))
      rcases nonzero_restriction_of_prod q2 hls with hl | hs
      · rcases simple_quotient_of_extension i₂ π₂ hπ₂ he₂ _ hl with hn | hd
        · exact Or.inr (Or.inl hn)
        · exact Or.inr (Or.inr (Or.inl hd))
      · let q3 := q2.comp (IntertwiningMap.inr (ZMod 2) η γ)
        rcases IsIrreducible.bijective_or_eq_zero q3 with hbij | hz
        · exact Or.inr (Or.inr (Or.inr ⟨(q3.ofBijective hbij).symm⟩))
        · exact False.elim (hs hz)


end BinaryLinearThree.IrreducibleCatalogue
