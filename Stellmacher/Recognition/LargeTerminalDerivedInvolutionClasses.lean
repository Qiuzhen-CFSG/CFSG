module

public import Stellmacher.Recognition.LargeTerminalDerivedIntersectionFusion

/-!
# Assembling the derived involution alternative

The actual common elementary eight has the desired fusion-or-centralizer
alternative by its native full plane action. Conjugation preserves centralizer
orders, and every derived involution fuses into that intersection by the
faithful Frobenius action on the order-sixteen central quotient. This proves
the full alternative directly from the retained large terminal context.

Source: Thompson VI, printed pp.627--630, the three local orbits represented
by Z, Z*, K and the cubic element centralizing K.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven Subgroup
universe u

private theorem centralizer_card_eq_of_isConj
    {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  let f : centralizer ({x} : Set G) ≃ centralizer ({e x} : Set G) := {
    toFun a := ⟨e a, by
      rw [mem_centralizer_singleton_iff]
      simpa only [map_mul] using
        congrArg e (mem_centralizer_singleton_iff.mp a.property)⟩
    invFun a := ⟨e.symm a, by
      rw [mem_centralizer_singleton_iff]
      apply e.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using
        mem_centralizer_singleton_iff.mp a.property⟩
    left_inv a := Subtype.ext (e.symm_apply_apply a)
    right_inv a := Subtype.ext (e.apply_symm_apply a) }
  exact Nat.card_congr f

/-- It remains to fuse each derived involution into the common elementary
eight. The plane action proves the full alternative once that fusion is known. -/
public theorem LargeTerminalContext.derived_involution_alternative_of_intersection_fusion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (hfusion : ∀ t : G, t ∈ DerivedAmbient ctx.firstResidual → orderOf t = 2 →
      ∃ x : G, x ∈ ctx.derivedIntersection ∧ IsConj t x) :
    ∀ t : G, t ∈ DerivedAmbient ctx.firstResidual → orderOf t = 2 →
      IsConj z t ∨ 3 ∣ Nat.card (centralizer ({t} : Set G)) := by
  intro t ht htorder
  obtain ⟨x, hx, htx⟩ := hfusion t ht htorder
  have hxorder : orderOf x = 2 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp htx
    exact ((MulAut.conj g).orderOf_eq t).trans htorder
  rcases ctx.derived_intersection_involution_alternative z hz hgen x hx hxorder with hc | hd
  · exact Or.inl (hc.trans htx.symm)
  · exact Or.inr ((centralizer_card_eq_of_isConj htx).symm ▸ hd)

/-- Every derived-residual involution either fuses to the omega-central
involution or has ambient centralizer order divisible by three. The large
terminal context alone suffices; no ambient Sylow-five assumptions are used. -/
public theorem LargeTerminalContext.derived_involution_alternative
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∀ t : G, t ∈ DerivedAmbient ctx.firstResidual → orderOf t = 2 →
      IsConj z t ∨ 3 ∣ Nat.card (centralizer ({t} : Set G)) :=
  ctx.derived_involution_alternative_of_intersection_fusion z hz hgen
    (fun t ht _ => ctx.derived_fusion_into_intersection t ht)

end Stellmacher.Recognition
