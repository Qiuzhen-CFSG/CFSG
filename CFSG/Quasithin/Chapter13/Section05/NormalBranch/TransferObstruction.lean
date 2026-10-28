module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import Theory.Frattini.Intersection

/-!
# The final Frattini obstruction in 13.5.16

F.9.2 places Φ(U_H) in the original order-two line V₁. Functoriality
of Frattini subgroups of finite two-groups therefore bounds Φ(X) by
two whenever an actual conjugate of X lies in U_H. This contradicts
the order-four Φ(X)=V₂ constructed at the end of 13.5.16.

The source fusion and transfer argument must still produce X, its
Frattini subgroup, and its conjugate containment. None is inferred
from a family label or an arbitrary group of the right order.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
last paragraph of Proposition 13.5.16, printed p.922 (PDF p.939).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G}

/-- Any subgroup whose conjugate enters U_H has Frattini subgroup of order ≤2. -/
theorem frattini_card_le_two_of_conjugate_le (h : D.Hypothesis)
    (X : Subgroup G) (r : G)
    (hX : X.map (MulAut.conj r⁻¹).toMonoidHom ≤ D.UH) :
    Nat.card (frattini X) ≤ 2 := by
  let f := (MulAut.conj r⁻¹).toMonoidHom
  have hi : Function.Injective f := (MulAut.conj r⁻¹).injective
  have hf : ((frattini X).map X.subtype).map f ≤ D.V₁ := by
    rw [← frattini_image_map X f hi]
    exact (frattini_image_le_of_le hX h.g2_hypothesis.U_isPGroup).trans
      h.frattini_UH_le_point
  have hc := card_le_of_le hf
  rw [card_map_of_injective hi, card_map_of_injective X.subtype_injective,
    h.point_card] at hc
  exact hc

/-- The literal final contradiction: Φ(X)=V₂ has order four. -/
theorem four_frattini_conjugate_obstruction (h : D.Hypothesis)
    (X V₂ : Subgroup G) (r : G)
    (hphi : (frattini X).map X.subtype = V₂)
    (hfour : Nat.card V₂ = 4)
    (hX : X.map (MulAut.conj r⁻¹).toMonoidHom ≤ D.UH) : False := by
  have hc : Nat.card (frattini X) = 4 := by
    rw [← hphi, card_map_of_injective X.subtype_injective] at hfour
    exact hfour
  have hb := frattini_card_le_two_of_conjugate_le h X r hX
  omega

end CFSG.Quasithin.Chapter13.Section05.NormalBranch
end
