module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitarySourceMarkingGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitarySource
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoverage
public import Theory.GroupTheory.SylowMarkedCenterLifting
public import Theory.SpecificGroups.SU3.QuinticSylow
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.SpecificGroups.SU3.QuinticRootCenter

/-!
# The unitary-five exclusion with corrected secondary source data

Moved-core generation supplies an inner radical involution centralizing the
original secondary quintic. The concrete PSU₃(5) root theorem places that
quintic at a Sylow center. Coprime lifting through O₂(K_Z) retains its placement
in K₂ and both subtype maps to G, yielding the actual extraspecial 125-group.

The original root coordinates discharge generation, and the checked bound
on the entire R₂ gives the terminal contradiction. Thus the final application
requires neither a Sylow-center marking nor a generation premise: its inputs
are the MS data, corrected secondary geometry and original marked parabolic.
Construction of those data and the other branches of the original nonblock
theorem remain with `qt-d-1222-rankone-uniqueness-nonblock`.
No legacy SecondaryData witness is constructed or used.
Source: Aschbacher--Smith, conclusion of original 4.3.2, printed p.618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
open EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The original component inclusion, through the original root normalizer. -/
abbrev unitaryComponentEmbedding (s : SecondarySourceData c n) : s.component →* G :=
  (rootNormalizer c).subtype.comp s.component.subtype

/-- Placement in the literal two-core quotient, proved below from the
original radical action and used in the coprime Sylow-center lift. -/
def UnitaryFiveQuotientPlacement (s : SecondarySourceData c n) : Prop :=
  ∃ P : Sylow 5 (s.component ⧸ pCore 2 s.component),
    (center P).map (P : Subgroup _).subtype ≤
      ((secondary c).comap (unitaryComponentEmbedding s)).map
        (QuotientGroup.mk' (pCore 2 s.component))

private theorem quotient_sylow_structure (s : SecondarySourceData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (P : Sylow 5 (s.component ⧸ pCore 2 s.component)) :
    IsExtraspecial 5 P ∧ Nat.card P = 5 ^ 3 := by
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hunitary
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let d : P ≃* P' := (P : Subgroup _).equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨he, hcard⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.QuinticSylow.extraspecial_card J hF hc P'
  exact ⟨IsExtraspecial.of_mulEquiv d.symm he, (Nat.card_congr d.toEquiv).trans hcard⟩

/-- Lift the actual quotient center into K₂ and retain the original component Sylow.
Only the quotient placement remains a geometric premise. -/
theorem unitaryFive_marking_of_quotient_placement (s : SecondarySourceData c n)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hplace : UnitaryFiveQuotientPlacement s) : Nonempty (UnitaryFiveMarking s) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let f := QuotientGroup.mk' (pCore 2 s.component)
  have hker : Nat.Coprime 5 (Nat.card f.ker) := by
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := s.component)).exists_card_eq
    rw [QuotientGroup.ker_mk', hk]
    exact (by decide : Nat.Coprime 5 2).pow_right k
  obtain ⟨P, hP⟩ := hplace
  obtain ⟨Q, hQP, hQZ⟩ := exists_sylow_center_le_of_coprime f
    (QuotientGroup.mk'_surjective _) hker
    ((secondary c).comap (unitaryComponentEmbedding s)) P hP
  let e : Q ≃* P :=
    (MulEquiv.ofBijective (f.subgroupMap (Q : Subgroup s.component)) ⟨by
      intro x y hxy
      exact injective_comp_subtype_of_coprime_ker f hker _ Q.isPGroup'
        (congrArg Subtype.val hxy), f.subgroupMap_surjective _⟩).trans
      (MulEquiv.subgroupCongr hQP)
  obtain ⟨hPe, hPc⟩ := quotient_sylow_structure s hunitary P
  let i := unitaryComponentEmbedding s
  have hi : Function.Injective i :=
    (rootNormalizer c).subtype_injective.comp s.component.subtype_injective
  let A := (Q : Subgroup s.component).map i
  let a : Q ≃* A := (Q : Subgroup s.component).equivMapOfInjective i hi
  refine ⟨{
    actor := A
    le_component := ?_
    extraspecial := IsExtraspecial.of_mulEquiv (e.symm.trans a) hPe
    card := (Nat.card_congr (e.symm.trans a).toEquiv).symm.trans hPc
    center_le_secondary := ?_
    sylow := ⟨Q, by rw [map_map]⟩ }⟩
  · change (Q : Subgroup s.component).map
      ((rootNormalizer c).subtype.comp s.component.subtype) ≤ _
    rw [← map_map]
    exact map_mono (map_subtype_le _)
  · rw [← map_embeddedCenter (Q : Subgroup s.component) i hi]
    exact (map_mono hQZ).trans (map_comap_le _ _)

/-- The literal image of K₂ contains a Sylow five-center in the component quotient. -/
theorem unitaryFive_quotient_placement (s : SecondarySourceData c 2)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    UnitaryFiveQuotientPlacement s := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨X, hX, hXB, t, ht, hXt⟩ := unitaryFive_quotient_involution_witness s hunitary hgen
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
  exact ⟨SourceImages.secondaryToComponent c s.component s.secondary_le x, x.property, rfl⟩

/-- The actual extraspecial Sylow five-group with center in the original K₂.
The witness retains both original subtype maps. -/
theorem unitaryFive_marking (s : SecondarySourceData c 2)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    Nonempty (UnitaryFiveMarking s) :=
  unitaryFive_marking_of_quotient_placement s hunitary
    (unitaryFive_quotient_placement s hunitary hgen)

/-- Both original subtype maps carry a component Sylow onto an extraspecial
125-group whose order-five center is an actual subgroup of the original K₂. -/
theorem unitaryFive_marked_center (s : SecondarySourceData c 2)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hgen : Q c ⊔ ⁅R₂ c, secondary c⁆ = R₂ c) :
    ∃ (P : Sylow 5 s.component) (X : Subgroup G),
      let A := ((P : Subgroup s.component).map s.component.subtype).map
        (rootNormalizer c).subtype
      IsExtraspecial 5 A ∧ Nat.card A = 125 ∧
        (center A).map A.subtype = X ∧ X ≤ secondary c ∧ Nat.card X = 5 := by
  obtain ⟨m⟩ := unitaryFive_marking s hunitary hgen
  obtain ⟨P, hP⟩ := m.sylow
  refine ⟨P, (center m.actor).map m.actor.subtype, ?_⟩
  dsimp only
  rw [hP]
  refine ⟨m.extraspecial, m.card, rfl, m.center_le_secondary, ?_⟩
  let : IsExtraspecial 5 m.actor := m.extraspecial
  rw [card_map_of_injective m.actor.subtype_injective]
  exact IsExtraspecial.center_order_p 5 m.actor

/-- The actual natural coordinates discharge the generation premise of the
corrected Sylow-center construction. -/
theorem unitaryFive_marking_of_coordinates (d : MSData c 2)
    (s : SecondarySourceData c 2) (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) :
    Nonempty (UnitaryFiveMarking s) :=
  unitaryFive_marking s hunitary (m.radical_generation (by decide) D s.core_eq)

/-- The source unitary exclusion discharges both the actual Sylow marking
and the four-factor bound on the whole literal radical. -/
theorem unitaryFive_false_of_source_data (d : MSData c 2)
    (s : SecondarySourceData c 2) (m : RootCoordinates d)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) : False := by
  obtain ⟨marking⟩ := unitaryFive_marking_of_coordinates d s m D hunitary
  exact unitaryFive_false_of_source_marking d s D h marking

/-- On the original line-parabolic and Sylow markings, the unitary-five branch
is impossible. Root coordinates, whole-radical generation, quintic placement
and the numerical bound have all been discharged. -/
theorem unitaryFive_false_of_marked_parabolic (d : MSData c 2)
    (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5)
    (hL : (L.subgroupOf (K c)).map
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor d.model) =
        Matrix.PSL3.LinearThree.lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.linearThreeActor d.model) =
        Matrix.PSL3.LinearThree.unipotentSL d.field.Carrier) : False := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact unitaryFive_false_of_source_data d s m D h hunitary

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
