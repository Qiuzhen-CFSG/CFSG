module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients

/-!
# The PSL₂(4) overlap in the Lie-type sieve

The two projective models are identified through the genuine alternating
five-group equivalences. Parameter five is a Fermat prime. Independently,
every automorphism fixing a Sylow four-group pointwise is conjugation by
an element of that four-group. Thus the actual V-action image has order
at most four, and V/C_V(L) has binary corank at most two.

These deductions retain both possible positive action coranks. They do not
assert U = C_V(L), corank one, or the odd alternative: the exceptional
branch still requires its local subgroup argument. In particular a model
comparison does not discharge the action clauses of E.6.8(5).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), especially the explicit L₂(4) to L₂(5)
transition on p.248.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve

variable {G : Type*} [Group G] [Finite G] {V L : Subgroup G}

omit [Finite G] in
/-- The exceptional model comparison is a composition of actual projective
matrix-group equivalences through A₅. -/
theorem five_model_of_four (hm : ClassicalGroup.IsPSL L 2 4) :
    ClassicalGroup.IsPSL L 2 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨ZMod 5, inferInstance, inferInstance, Nat.card_zmod 5,
    ⟨(e.trans e₄).trans e₅.symm⟩⟩

omit [Finite G] in
/-- Parameter five satisfies the literal Fermat condition in E.6.8(5). -/
theorem odd_model_of_four (hm : ClassicalGroup.IsPSL L 2 4) :
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p := by
  exact ⟨5, ⟨by decide, Or.inl ⟨1, by norm_num⟩⟩, five_model_of_four hm⟩

/-- Fixing the actual Sylow four-group pointwise bounds the induced
conjugation image by that four-group. No rank-one assertion is made. -/
theorem action_image_card_le_four (hm : ClassicalGroup.IsPSL L 2 4)
    (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    Nat.card (inducedAutomizer L V) ≤ 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eA := e.trans e₄
  let J := (inducedAutomizer L V).map (Automizer L).subtype
  have hJ : J ≤ (S : Subgroup L).map (MulAut.conj : L →* MulAut L) := by
    rintro a ⟨b, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨x, hx, he⟩ :=
      Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five eA S
        (L.normalizerMonoidHom v) (by
          intro s hs
          apply Subtype.ext
          exact hfix v hv ⟨s, hs⟩)
    exact ⟨x, hx, he.symm⟩
  calc
    Nat.card (inducedAutomizer L V) = Nat.card J :=
      (Subgroup.card_map_of_injective (Automizer L).subtype_injective).symm
    _ ≤ Nat.card ((S : Subgroup L).map (MulAut.conj : L →* MulAut L)) :=
      Nat.card_le_card_of_injective (inclusion hJ) (inclusion_injective hJ)
    _ ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos
      ((S : Subgroup L).card_map_dvd (MulAut.conj : L →* MulAut L))
    _ = 4 := Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five eA S

/-- The quotient V/C_V(L) has binary corank at most two when L is PSL₂(4)
and V fixes its Sylow subgroup pointwise. -/
theorem actionCorank_le_two (hm : ClassicalGroup.IsPSL L 2 4)
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    actionCorank V L ≤ 2 := by
  rw [actionCorank, ← rank_inducedAutomizer L V hN]
  exact (Nat.log_mono_right (action_image_card_le_four hm S hfix)).trans (by decide)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve
