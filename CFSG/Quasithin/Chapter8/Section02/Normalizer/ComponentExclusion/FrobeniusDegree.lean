module

public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.Representation.ElementaryAbelianAction

/-!
# The character-orbit obstruction for the containing component

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the final sentence of Lemma 8.2.7, printed p.718.

An odd abelian subgroup with a fixed-point-free normalizing subgroup of
order 24 forces every faithful binary module to have dimension at least 24.
Here the group is a literal subgroup of Aut(W), so its action on the
canonical binary vector space of W is proved faithful. The character-orbit
bound works without assuming irreducibility or a chosen splitting field.

This is the degree calculation once the actual extension supplies these
two subgroups. Their construction for the source SL₂(q)/E_(p²) extension,
including the SL₂(5) alternatives with p ≠ 5, remains a separate obligation.
No assertion about an arbitrary group with that quotient alone is made.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
open Subgroup
open scoped IsMulCommutative

/-- The actual automorphism action has degree at least 24 when it contains
the odd abelian kernel and a free normalizer subgroup of order 24. -/
theorem actionImage_finrank_ge_twentyFour {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (A : Subgroup (MulAut W)) (N C : Subgroup A)
    [Nontrivial N] [IsMulCommutative N]
    (hodd : Odd (Nat.card N)) (hcard : Nat.card C = 24)
    (hnorm : C ≤ normalizer (N : Set A))
    (hfree : ∀ c : C, c ≠ 1 → ∀ n : N,
      (c : A) * n * (c : A)⁻¹ = n → n = 1) :
    24 ≤ Module.finrank (ZMod 2) (Additive W) := by
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := W) (p := 2)
  have hf : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    ext w
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul w)) hab)
  have hn : (Nat.card N : ZMod 2) ≠ 0 := by
    exact ZMod.natCast_ne_zero_iff_odd.mpr hodd
  have hd := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field
    ρ N C hf hn hnorm hfree
  rwa [hcard] at hd

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion
