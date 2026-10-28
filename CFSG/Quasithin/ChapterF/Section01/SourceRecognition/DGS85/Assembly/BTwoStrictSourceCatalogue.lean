module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictSourceQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictRootSigns
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictLinearCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2Native
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNative

/-!
# The full strict linear catalogue with source-constructed reflections

The source supplies both reflections at its chosen compatible Cartan. Apply
the full linear hexagon comparison to that exact choice. Equal-field G₂ and
unequal-field triality remain in the conclusion; no common-field hypothesis
or model recognition input is imposed. The original explicit-sign interface
is retained. The exchange-only theorems discharge the whole-original-Borel
root signs by the raw hexagon root-rigidity argument.
The native two-row conclusion also retains the exact reduced diagrams needed
by the existing original-Borel restoration theorems at Chapter 12.

Source: DGS (1985), (10.10), p.164, (14.1)--(14.2), pp.210--211,
Theorem D, p.224; Fong--Seitz I (6E), pp.43--45.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
  (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear)
  (hsign : StrictSourceRootSigns h hc hne hb hβu hns hlinear)

include h hc hne hb hβu hns hlinear hexchange hsign in
/-- Retain the two exact native hexagon rows so that an actual source
consumer can restore its original Borel from the reduced comparison. -/
theorem strict_source_linear_hexagon_native_alternatives :
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (short : Bool),
      Nonempty (Iso (reducedAmalgam L S) (G2Native.amalgam K short))) ∨
    (∃ (m : ℕ) (hm : 0 < m) (point : Bool),
      Nonempty (Iso (reducedAmalgam L S) (TrialityNative.amalgam m hm point))) := by
  have hval : 3 ≤ Nat.card ((graph (reducedFamily L S)).neighborSet
      (base (reducedFamily L S) false)) := by
    rw [card_neighbors_of_indices (reducedFamily L S)
      (fun i => (((reducedFamily L S) (!i)).subgroupOf ((reducedFamily L S) i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) false
  obtain ⟨v,hv,hvne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph (reducedFamily L S)).neighborSet (base (reducedFamily L S) false))
    (by rw [←Nat.card_coe_set_eq]; omega) (base (reducedFamily L S) true)
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,m,hm,hright,_⟩ :=
    original_core_layers h hc hne hb hβu hv hvne hns
  have hleft := hlinear
  obtain ⟨K₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hleft
  obtain ⟨K₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := hright
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ := Fintype.ofFinite K₀
  let _ := Fintype.ofFinite K₁
  let _ : CharP K₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP K₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let j : Iso
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam L (reducedSylow L S))
      (reducedAmalgam L S) :=
    NativeRestoration.subgroupCongrIso _ _ _ _ rfl
      (lemma_F_1_3_6 (reduced_hypothesis h)) rfl
  let Q := strictSourceFiniteQuotient h hc hne hb hβu hns hlinear hexchange hsign
  let mark := j.trans
    (strictSourceFiniteMarkedIso h hc hne hb hβu hns hlinear hexchange hsign)
  let split := strictSourceFiniteSplitData h hc hne hb hβu hns hlinear hexchange hsign
  have hrot := strictSourceFiniteQuotient_rotation h hc hne hb hβu hns hlinear hexchange hsign
  obtain ⟨a,_,ha⟩ := FiniteField.card K₀ 2
  obtain ⟨b,_,hbfield⟩ := FiniteField.card K₁ 2
  have hK₀ : Nat.card K₀ = 2^(a : ℕ) := by simpa only [Nat.card_eq_fintype_card] using ha
  have hK₁ : Nat.card K₁ = 2^(b : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hbfield
  rcases lt_trichotomy (a : ℕ) b with hab | hab | hab
  · obtain ⟨_,⟨e⟩⟩ := LinearHexagon.marked_unequal_linear_triality
      Q mark (reduced_hypothesis h) split hrot 0 1 (by decide) e₀ e₁
      a.property hab hK₀ hK₁
    exact Or.inr ⟨a,a.property,true,⟨j.symm.trans e⟩⟩
  · have hcard : Nat.card K₀ = Nat.card K₁ := by rw [hK₀,hK₁,hab]
    obtain ⟨K,hK,hfin,hchar,_,e⟩ := LinearHexagon.marked_equal_linear_gTwo
      Q mark (reduced_hypothesis h) split hrot e₀ e₁ hcard
    rcases e with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨K,hK,hfin,hchar,true,
        ⟨j.symm.trans (e.trans GreenBook.LieModels.G2.borelIso)⟩⟩
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨K,hK,hfin,hchar,false,
        ⟨j.symm.trans (e.trans GreenBook.LieModels.G2.borelIso.reverse)⟩⟩
  · obtain ⟨_,⟨e⟩⟩ := LinearHexagon.marked_unequal_linear_triality
      Q mark (reduced_hypothesis h) split hrot 1 0 (by decide) e₁ e₀
      b.property hab hK₁ hK₀
    exact Or.inr ⟨b,b.property,false,⟨j.symm.trans e⟩⟩

/-- The original strict linear-left source gives the complete reduced
G₂/triality catalogue, with neither Cartan nor reflection choices assumed. -/
theorem strict_source_linear_hexagon_catalogue
    (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    (hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear)
    (hsign : StrictSourceRootSigns h hc hne hb hβu hns hlinear) :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam
        L (reducedSylow L S)) := by
  let d := strictSourceReflections h hc hne hb hβu hns hlinear
  exact strict_linear_hexagon_catalogue h hc hne hb hβu hns hlinear (chosenCartans h)
    d.t d.fixes d.moves d.square d.normalizes hexchange hsign

include h hc hne hb hβu hns hlinear hexchange in
/-- The two native strict rows with the whole-Borel root signs proved from
exchange on the literal source-selected apartment. -/
theorem strict_source_linear_hexagon_native_alternatives_of_exchange :
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (short : Bool),
      Nonempty (Iso (reducedAmalgam L S) (G2Native.amalgam K short))) ∨
    (∃ (m : ℕ) (hm : 0 < m) (point : Bool),
      Nonempty (Iso (reducedAmalgam L S) (TrialityNative.amalgam m hm point))) := by
  exact strict_source_linear_hexagon_native_alternatives h hc hne hb hβu hns hlinear
    hexchange (strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange)

include h hc hne hb hβu hns hlinear hexchange in
/-- The full reduced strict catalogue now requires only apartment exchange
as its geometric source input. -/
theorem strict_source_linear_hexagon_catalogue_of_exchange :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam
        L (reducedSylow L S)) := by
  exact strict_source_linear_hexagon_catalogue h hc hne hb hβu hns hlinear
    hexchange (strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange)

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
