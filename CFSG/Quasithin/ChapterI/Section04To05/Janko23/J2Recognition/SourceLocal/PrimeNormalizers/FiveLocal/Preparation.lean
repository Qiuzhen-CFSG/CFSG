module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Contracts

/-!
# The Sylow-five centralizer and the literal complement action

The two involution-centralizer orders from 47.1 exclude every involution
from C_G(P): an involution there would put the order-25 subgroup P inside
a centralizer of order 1920 or 240. Cauchy's theorem makes C_G(P) odd.

For the final split normalizer, restriction of the actual conjugation
homomorphism gives the action of its D₁₂ complement. Self-centralization
of P and the complement intersection prove this action faithful. The
complement itself and self-centralization remain outputs to be constructed
by the remaining branches of Aschbacher, *Sporadic Groups* (1994), 47.2.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_map (t : G) (e : G ≃* G) :
    (involutionCentralizer t).map e.toMonoidHom = involutionCentralizer (e t) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      map_centralizer_le_centralizer_image ({t} : Set G) e.toMonoidHom
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

omit [Finite G] in
private theorem centralizer_card_of_isConj {t u : G} (h : IsConj t u) :
    Nat.card (involutionCentralizer t) = Nat.card (involutionCentralizer u) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he := centralizer_map t (MulAut.conj g)
  rw [show MulAut.conj g t = u from hg] at he
  rw [← he, card_map_of_injective (MulAut.conj g).injective]

/-- The order alternatives for every involution, without a representative-placement assumption. -/
theorem involution_centralizer_card {D : Seed G} {t : G}
    (ht : InvolutionGeometry.OtherInvolution D t)
    (C : InvolutionGeometry.SecondCentralizer D t) (u : G) (hu : orderOf u = 2) :
    Nat.card (involutionCentralizer u) = 1920 ∨
      Nat.card (involutionCentralizer u) = 240 := by
  rcases ht.classes u hu with h | h
  · exact Or.inl ((centralizer_card_of_isConj h).symm.trans D.localType.centralizer_card)
  · exact Or.inr ((centralizer_card_of_isConj h).symm.trans C.centralizer_card)

/-- No involution can centralize the actual Sylow five-subgroup. -/
theorem no_involution_in_sylow_centralizer {D : Seed G} {t : G}
    (ht : InvolutionGeometry.OtherInvolution D t)
    (C : InvolutionGeometry.SecondCentralizer D t) (hG : Nat.card G = 604800)
    (P : Sylow 5 G) (u : G) (hu : orderOf u = 2) : u ∉ centralizer (P : Set G) := by
  intro hmem
  have hP : (P : Subgroup G) ≤ involutionCentralizer u := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hmem x hx)
  have hd := card_dvd_of_le hP
  rw [sylow_card hG P] at hd
  rcases involution_centralizer_card ht C u hu with h | h <;> rw [h] at hd <;>
    norm_num at hd

/-- Cauchy's theorem converts the preceding exclusion into the source oddness bound. -/
theorem sylow_centralizer_odd {D : Seed G} {t : G}
    (ht : InvolutionGeometry.OtherInvolution D t)
    (C : InvolutionGeometry.SecondCentralizer D t) (hG : Nat.card G = 604800)
    (P : Sylow 5 G) : Odd (Nat.card (centralizer (P : Set G))) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (P : Set G)) 2 h
  exact no_involution_in_sylow_centralizer ht C hG P u
    ((orderOf_coe u).trans hu) u.property

namespace SylowSplitWitness
variable {P : Sylow 5 G} (W : SylowSplitWitness P)

/-- The complement acts through literal ambient conjugation on P. -/
def action : W.complement →* MulAut P :=
  (P : Subgroup G).normalizerMonoidHom.comp W.complement.subtype

/-- The same actual action, with the specified D₁₂ carrier. -/
def dihedralAction : DihedralGroup 6 →* MulAut P :=
  W.action.comp W.equiv.symm.toMonoidHom

omit [Finite G] in
/-- The split complement acts faithfully when P is self-centralizing. -/
theorem action_injective (hC : centralizer (P : Set G) = (P : Subgroup G)) :
    Function.Injective W.action := by
  apply W.action.ker_eq_bot_iff.mp
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hxC : x.val ∈ (P : Subgroup G).normalizerMonoidHom.ker := hx
  rw [normalizerMonoidHom_ker] at hxC
  change (x.val : G) ∈ centralizer (P : Set G) at hxC
  rw [hC] at hxC
  have hi : x.val ∈ W.complement ⊓
      (P : Subgroup G).subgroupOf (normalizer (P : Set G)) := ⟨x.property, hxC⟩
  rw [W.isComplement.disjoint.eq_bot] at hi
  exact Subtype.ext (mem_bot.mp hi)

omit [Finite G] in
theorem dihedralAction_injective (hC : centralizer (P : Set G) = (P : Subgroup G)) :
    Function.Injective W.dihedralAction :=
  (W.action_injective hC).comp W.equiv.symm.injective

include W in
/-- The internal splitting gives the correct order 300 of the ambient normalizer. -/
theorem normalizer_card (hG : Nat.card G = 604800) :
    Nat.card (normalizer (P : Set G)) = 300 := by
  have hc := W.isComplement.card_mul_card
  have hp : Nat.card ((P : Subgroup G).subgroupOf (normalizer (P : Set G))) = 25 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show (P : Subgroup G) ≤
      normalizer (P : Set G) from le_normalizer)).toEquiv).trans (sylow_card hG P)
  rw [Nat.card_congr W.equiv.toEquiv, hp, DihedralGroup.nat_card] at hc
  exact hc.symm

end SylowSplitWitness
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
