module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitaryMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitaryMarkingGeometry
public import Theory.SpecificGroups.SU3.QuinticRootCenter

/-!
# The original quintic Sylow-center marking

The nontrivial original R₂ action supplies an involution centralizing an
order-five subgroup in the literal K₂ image. The concrete PSU₃(5) root
calculation identifies that subgroup with a Sylow center. Coprime lifting
through O₂(K_Z) puts the center inside the original K₂ and retains the
Sylow subgroup of K_Z and both subtype maps into G.

The source marking and its explicit order-five center are constructed here.
The final theorem supplies this marking to the existing characteristic-two
index contradiction. Its only extra source premise is the independent
four-chief-factor bound on R₂, coming from the natural and doubled-dual
modules and the parabolic quotient.

Source: Aschbacher--Smith, original 4.3.2, conclusion on printed p.618
(PDF p.635), with the original local data in 4.3.11--16 on pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- The literal image of K₂ contains a Sylow five-center in the component quotient. -/
theorem unitaryFive_quotient_placement (s : SecondaryData c 2)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    UnitaryFiveQuotientPlacement s := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨X, hX, hXB, t, ht, hXt⟩ := unitaryFive_quotient_involution_witness s hunitary
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hunitary
  have hx : Nat.card (X.map e.toMonoidHom) = 5 := by
    rw [card_map_of_injective e.injective, hX]
  have hn : X.map e.toMonoidHom ≤ centralizer ({e t} : Set _) := by
    simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using
      (map_mono (f := e.toMonoidHom) hXt).trans
        (map_centralizer_le_centralizer_image ({t} : Set _) e.toMonoidHom)
  obtain ⟨P, hP⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.QuinticRootCenter.center_eq_of_centralizes_involution_arbitrary
      J hF hc (X.map e.toMonoidHom) hx (e t) ((e.orderOf_eq t).trans ht) hn
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ : (center Q).map (Q : Subgroup _).subtype = X := by
    change (center ((P : Subgroup _).map e.symm.toMonoidHom)).map
      ((P : Subgroup _).map e.symm.toMonoidHom).subtype = X
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [← map_embeddedCenter (P : Subgroup _) e.symm.toMonoidHom e.symm.injective, hP,
      map_map, he, map_id]
  refine ⟨Q, hQ.le.trans (hXB.trans ?_)⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨SecondaryData.secondaryToComponent s x, x.property, rfl⟩

/-- The actual extraspecial Sylow five-group with center in the original K₂.
The witness retains both original subtype maps. -/
theorem unitaryFive_marking (s : SecondaryData c 2)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    Nonempty (UnitaryFiveMarking s) :=
  unitaryFive_marking_of_quotient_placement s hunitary
    (unitaryFive_quotient_placement s hunitary)

/-- Both original subtype maps carry a component Sylow onto an extraspecial
125-group whose order-five center is an actual subgroup of the original K₂. -/
theorem unitaryFive_marked_center (s : SecondaryData c 2)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    ∃ (P : Sylow 5 s.component) (X : Subgroup G),
      let A := ((P : Subgroup s.component).map s.component.subtype).map
        (rootNormalizer c).subtype
      IsExtraspecial 5 A ∧ Nat.card A = 125 ∧
        (center A).map A.subtype = X ∧ X ≤ secondary c ∧ Nat.card X = 5 := by
  obtain ⟨m⟩ := unitaryFive_marking s hunitary
  obtain ⟨P, hP⟩ := m.sylow
  refine ⟨P, (center m.actor).map m.actor.subtype, ?_⟩
  dsimp only
  rw [hP]
  refine ⟨m.extraspecial, m.card, rfl, m.center_le_secondary, ?_⟩
  let : IsExtraspecial 5 m.actor := m.extraspecial
  rw [card_map_of_injective m.actor.subtype_injective]
  exact IsExtraspecial.center_order_p 5 m.actor

/-- The source unitary branch now requires only the independent four-factor bound.
The original root-center placement and extraspecial Sylow construction are discharged. -/
theorem unitaryFive_false_of_unitary_and_bound (s : SecondaryData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hbound : QuinticRadicalBound c) : False := by
  obtain ⟨m⟩ := unitaryFive_marking s hunitary
  exact unitaryFive_false_of_marking_and_bound s D h m hbound

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
