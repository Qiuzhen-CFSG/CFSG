module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.Covers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve.ModelSeparation

/-!
# The degree-eight specialization of the universal FF table

The actual A₈ component excludes every other irreducible-table group and the
SL₃ double-natural case. In both remaining reducible branches the projective
parameter is four, not five. A four-dimensional natural quotient has zero
dual H¹; the universal-cover argument and `[V,L]=V` therefore turn it into
one natural summand. The orthogonal branch keeps the literal fixed-space
quotient and its kernel.

The theorem below is conditional only on the independently stated universal
classification and cohomology inputs in `Source`. It proves their complete
specialization; it does not prove those earlier universal theorems. No local
configuration, marking, moving line, or local recognition output is assumed.
The parent may instantiate it at its offender actor and component.

Source: Aschbacher–Smith, B.4.2, B.5.1(1), I.1.5–I.1.6(6), and the use in
15.3.32(1), printed pp.86, 99–103, 408 and 1132.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve
open Chapter2.ComponentRefinement.LieType.Binary

universe u v
variable {K : Type u} {V : Type v} [Group K] [Finite K]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) K V} {L : Subgroup K}

/-- The genuine universal FF classification specializes to the three published
unmarked outputs. The natural-cover kernel is discharged, while the orthogonal
fixed-space kernel is preserved. Both universal source inputs remain explicit. -/
theorem unmarkedCases (classification : UniversalFFClassification.{u,v})
    (cohomology : UniversalNaturalCohomology)
    (hFF : FFInput KnownSimple.IsKnownSimple ρ L)
    (alternating : L ≃* alternatingGroup (Fin 8)) : UnmarkedCases ρ L := by
  have hcard := card_of_alternating alternating
  have noFive (model : L ≃* PSL 5) : False :=
    psl_five_card_ne ((Nat.card_congr model.toEquiv).symm.trans hcard)
  rcases classification ρ L hFF with hi | hdouble | hdual | hrepeated | hrepeated
  · rcases hi with hother | hfour | hfive | horthogonal
    · exact (not_other_of_card hcard hother).elim
    · obtain ⟨hfour⟩ := hfour
      exact Or.inr (Or.inr ⟨1, by decide, by decide,
        hfour.repeated_one hFF.full cohomology⟩)
    · obtain ⟨hfive⟩ := hfive
      exact (noFive hfive.model).elim
    · exact Or.inl horthogonal
  · obtain ⟨f, hf, ⟨h⟩⟩ := hdouble
    exact (sl_three_card_ne f hf ((Nat.card_congr h.model.toEquiv).symm.trans hcard)).elim
  · rcases hdual with h | h
    · obtain ⟨h⟩ := h
      exact Or.inr (Or.inl ⟨h.model, ⟨{
        coordinates := h.coordinates
        equivariant := h.equivariant }⟩⟩)
    · obtain ⟨h⟩ := h
      exact (noFive h.model).elim
  · obtain ⟨r, hr, hb, ⟨h⟩⟩ := hrepeated
    exact Or.inr (Or.inr ⟨r, hr, hb, ⟨{
      model := h.model
      coordinates := h.coordinates
      equivariant := h.equivariant }⟩⟩)
  · obtain ⟨_, _, _, ⟨h⟩⟩ := hrepeated
    exact (noFive h.model).elim

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.Sieve

end
