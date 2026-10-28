module

public import CFSG.Quasithin.Defs

/-!
# Sections and the order measure for simultaneous induction

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2, printed pp.34–38. A section is a surjective
image of a subgroup, exactly as in the shared K-group definition. Its kernel
is normal in that subgroup, with no ambient normality requirement. Properness
for the finite-group induction is strict decrease of group order.

The proofs compose or lift surjections. Lagrange's formula proves strict
decrease for nontrivial quotients; subgroup cardinality proves it for proper
subgroups and their sections. Thus the induction size premises have elementary
discharge lemmas, rather than encoding a classification conclusion.
-/

@[expose] public section

universe u v w

namespace CFSG.Quasithin.ChapterA.Section02

/-- S is isomorphic to a quotient of an actual subgroup of G. -/
def IsSectionOf (S : Type u) (G : Type v) [Group S] [Group G] : Prop :=
  ∃ (U : Subgroup G) (f : U →* S), Function.Surjective f

/-- A strictly smaller section, with size measured by the order of the group. -/
def IsProperSectionOf (S : Type u) (G : Type v) [Group S] [Group G] : Prop :=
  IsSectionOf S G ∧ Nat.card S < Nat.card G

variable {S : Type u} {H : Type v} {G : Type w} [Group S] [Group H] [Group G]

theorem IsSectionOf.of_surjective (f : G →* S) (hf : Function.Surjective f) :
    IsSectionOf S G :=
  ⟨⊤, f.comp Subgroup.topEquiv.toMonoidHom, hf.comp Subgroup.topEquiv.surjective⟩

theorem IsSectionOf.refl : IsSectionOf G G :=
  .of_surjective (MonoidHom.id G) Function.surjective_id

theorem IsSectionOf.subgroup (U : Subgroup G) : IsSectionOf U G :=
  ⟨U, MonoidHom.id U, Function.surjective_id⟩

theorem IsSectionOf.quotient_subgroup (U : Subgroup G) (N : Subgroup U) [N.Normal] :
    IsSectionOf (U ⧸ N) G :=
  ⟨U, QuotientGroup.mk' N, QuotientGroup.mk'_surjective N⟩

/-- The quotient witnessing a section has a kernel normal in its numerator. -/
theorem IsSectionOf.exists_quotient_equiv (h : IsSectionOf S G) :
    ∃ (U : Subgroup G) (f : U →* S), Nonempty ((U ⧸ f.ker) ≃* S) := by
  obtain ⟨U, f, hf⟩ := h
  exact ⟨U, f, ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

theorem IsSectionOf.finite [Finite G] (h : IsSectionOf S G) : Finite S := by
  obtain ⟨U, f, hf⟩ := h
  exact Finite.of_surjective f hf

theorem IsSectionOf.card_le [Finite G] (h : IsSectionOf S G) :
    Nat.card S ≤ Nat.card G := by
  obtain ⟨U, f, hf⟩ := h
  exact (Nat.card_le_card_of_surjective f hf).trans U.card_le_card_group

theorem IsSectionOf.of_mulEquiv (h : IsSectionOf S G) (e : H ≃* S) : IsSectionOf H G := by
  obtain ⟨U, f, hf⟩ := h
  exact ⟨U, e.symm.toMonoidHom.comp f, e.symm.surjective.comp hf⟩

/-- Embed the numerator into a larger ambient group. -/
theorem IsSectionOf.ambient_injective (h : IsSectionOf S H)
    (f : H →* G) (hf : Function.Injective f) : IsSectionOf S G := by
  obtain ⟨U, g, hg⟩ := h
  let e := Subgroup.equivMapOfInjective U f hf
  exact ⟨U.map f, g.comp e.symm.toMonoidHom, hg.comp e.symm.surjective⟩

/-- Lift the numerator through a surjective ambient homomorphism. -/
theorem IsSectionOf.ambient_surjective (h : IsSectionOf S H)
    (f : G →* H) (hf : Function.Surjective f) : IsSectionOf S G := by
  obtain ⟨U, g, hg⟩ := h
  exact ⟨U.comap f, g.comp (f.subgroupComap U),
    hg.comp (f.subgroupComap_surjective_of_surjective U hf)⟩

theorem IsSectionOf.trans (hSH : IsSectionOf S H) (hHG : IsSectionOf H G) :
    IsSectionOf S G := by
  obtain ⟨U, f, hf⟩ := hHG
  exact (hSH.ambient_surjective f hf).ambient_injective U.subtype U.subtype_injective

theorem IsProperSectionOf.of_mulEquiv (h : IsProperSectionOf S G) (e : H ≃* S) :
    IsProperSectionOf H G := by
  refine ⟨h.1.of_mulEquiv e, ?_⟩
  exact (Nat.card_congr e.toEquiv).trans_lt h.2

theorem IsProperSectionOf.subgroup [Finite G] (U : Subgroup G) (hU : U ≠ ⊤) :
    IsProperSectionOf U G :=
  ⟨.subgroup U, lt_of_not_ge fun h => hU (U.eq_top_of_le_card h)⟩

theorem IsSectionOf.proper_of_proper_subgroup [Finite G] {U : Subgroup G}
    (h : IsSectionOf S U) (hU : U ≠ ⊤) : IsProperSectionOf S G :=
  ⟨h.trans (.subgroup U), h.card_le.trans_lt (IsProperSectionOf.subgroup U hU).2⟩

theorem IsProperSectionOf.quotient [Finite G] (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    IsProperSectionOf (G ⧸ N) G := by
  refine ⟨.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N), ?_⟩
  have hcard := N.card_eq_card_quotient_mul_card_subgroup
  have hn := N.one_lt_card_iff_ne_bot.mpr hN
  have hq : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  calc
    Nat.card (G ⧸ N) < Nat.card (G ⧸ N) * Nat.card N := by
      simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hn hq
    _ = Nat.card G := hcard.symm

theorem IsProperSectionOf.trans
    (hSH : IsProperSectionOf S H) (hHG : IsProperSectionOf H G) :
    IsProperSectionOf S G :=
  ⟨hSH.1.trans hHG.1, hSH.2.trans hHG.2⟩

theorem IsSectionOf.proper_trans [Finite H]
    (hSH : IsSectionOf S H) (hHG : IsProperSectionOf H G) : IsProperSectionOf S G :=
  ⟨hSH.trans hHG.1, hSH.card_le.trans_lt hHG.2⟩

/-- K-group inheritance needs no invariance assumption on K. -/
theorem IsSectionOf.isKGroup {S G : Type u} [Group S] [Group G]
    {K : GroupClass.{u}} (h : IsSectionOf S G) (hK : IsKGroup K G) : IsKGroup K S := by
  obtain ⟨U, f, hf⟩ := h
  exact (hK.subgroup U).of_surjective f hf

end CFSG.Quasithin.ChapterA.Section02
