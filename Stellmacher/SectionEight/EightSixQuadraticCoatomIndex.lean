module
public import Stellmacher.SectionEight.EightSixNonquadraticActor
/-!
A quadratic subgroup A0 of index two in the predecessor actor A forces
|A:A intersect D|=4 in the large-index configuration of Stellmacher (8.6).
It also has |A0:A0 intersect D|=2 and contains A intersect D. The theorem
retains the actual equation-one packet and the explicit quadratic-action
premise; the separate cost-four coatom theorem supplies that premise.

Source (5) bounds the quadratic image of A0 by two. Its intersection with D
is contained in A intersect D, whereas source (7) bounds the actor image
below by four. The index-two coatom equality forces equality throughout.
This is the exact numerical step in the cost-four paragraph, printed p.44.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_quadratic_coatom_index_four
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (equation : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (A0 : Subgroup G)
    (hA0 : A0 ≤ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hcoatom : Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G) =
      2 * Nat.card A0)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hquad : ⁅⁅VAt ctx.Γ ctx.criticalPath.firstStep,A0⁆,A0⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep) :
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    QuotientCardEq A (A ⊓ D) 4 ∧ QuotientCardEq A0 (A0 ⊓ D) 2 ∧ A ⊓ D ≤ A0 := by
  let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
  have hbound := eight_six_nonquadratic_actor_local ctx hcenter hquot hlength hcard
    previous D L Q hprev hD equation A0 hA0 hquad
  have hle : A0 ⊓ D ≤ A ⊓ D := inf_le_inf hA0 le_rfl
  have hcardle := Subgroup.card_le_of_le hle
  have hmain : Nat.card A = 4 * Nat.card (A ⊓ D : Subgroup G) := by
    change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
    change Nat.card A = 2 * Nat.card A0 at hcoatom
    omega
  have hpart : Nat.card A0 = 2 * Nat.card (A0 ⊓ D : Subgroup G) := by
    change Nat.card A = 2 * Nat.card A0 at hcoatom
    omega
  have heq : A0 ⊓ D = A ⊓ D := Subgroup.eq_of_le_of_card_ge hle (by
    change Nat.card A = 2 * Nat.card A0 at hcoatom
    omega)
  exact ⟨hmain,hpart,heq ▸ inf_le_left⟩

end Stellmacher.SectionEight
