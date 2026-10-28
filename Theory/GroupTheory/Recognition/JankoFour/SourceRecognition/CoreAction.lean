module

public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Sylow
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The faithful action on the extraspecial central quotient

The canonical conjugation action of H = C_G(z) on Q/Z(Q) has kernel Q.
Indeed Q is the self-centralizing two-core, and its Frattini subgroup is its
center, so the Burnside–Frattini kernel theorem applies. Factoring this exact
action through H/Q gives a faithful action on the elementary central quotient
of order 2¹². The evaluation theorem retains the original conjugation map.

This is the faithful binary action at the start of the proof of (4.1).
Identifying it with the specific six-dimensional GF(4) module remains a
separate obligation; faithfulness alone does not give that identification.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), §4, printed p.597.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}

noncomputable def coreAction (z : G) :
    centralizer z →* MulAut (core z ⧸ center (core z)) :=
  (quotientAut (center (core z))).comp MulAut.conjNormal

private theorem extraspecial_coreAction_kernel {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal] [IsExtraspecial 2 Q] (hQ : Q = pCore 2 H)
    (hc : Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    ((quotientAut (center Q)).comp (MulAut.conjNormal : H →* MulAut Q)).ker = Q := by
  subst Q
  have hp := pCore_frattini_action_kernel 2 hc
  rw [← MonoidHom.comap_ker,
    IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := 2)] at hp
  rw [← MonoidHom.comap_ker,
    IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2)]
  exact hp

theorem coreAction_kernel (h : IsTypeJ4 z) : (coreAction z).ker = core z := by
  let := h.extraspecial
  exact extraspecial_coreAction_kernel (core z) h.core_eq_twoCore h.twoCore_selfCentralizing

noncomputable def coreQuotientAction (h : IsTypeJ4 z) :
    (centralizer z ⧸ core z) →* MulAut (core z ⧸ center (core z)) :=
  QuotientGroup.lift (core z) (coreAction z) (coreAction_kernel h).ge

theorem coreQuotientAction_injective (h : IsTypeJ4 z) :
    Function.Injective (coreQuotientAction h) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (coreAction_kernel h).symm

@[simp] theorem coreQuotientAction_mk (h : IsTypeJ4 z) (g : centralizer z)
    (q : core z) :
    coreQuotientAction h (QuotientGroup.mk' (core z) g)
        (QuotientGroup.mk' (center (core z)) q) =
      QuotientGroup.mk' (center (core z)) (MulAut.conjNormal g q) := by
  exact quotientAut_apply_mk _ _ _

theorem coreCentralQuotient_card (h : IsTypeJ4 z) :
    Nat.card (core z ⧸ center (core z)) = 2 ^ 12 := by
  let := h.extraspecial
  have hh := card_eq_card_quotient_mul_card_subgroup (center (core z))
  rw [h.core_card, IsExtraspecial.center_order_p 2 (core z)] at hh
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition

end
