module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarSpace
/-!
# The actual sextet residue as a binary symplectic quadrangle

Label the six tetrads of a native sextet. Unions of tetrad pairs identify its
incident octad trios with the fifteen perfect matchings on six letters. The
inverse constructs the actual octads, so the correspondence is an equivalence,
not merely an abstract family identification. Shared octads give collinearity
of singular lines in the four-dimensional binary symplectic space; this is the
dual orientation used in AS91 §7.

Source: Aschbacher–Segev (1991), §§2–3 and (7.3), pp.592–596,603.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Theory.SpecificGroups.SymmetricSix
open Finset

variable (π : Plane) (e : Fin 6 ≃ {A // A ∈ π.parts})

def tetradUnion (s : Finset (Fin 6)) : Finset (Fin 24) :=
  s.biUnion (fun i => (e i).val)

theorem tetradUnion_mem (s : Finset (Fin 6)) (i : Fin 6) :
    (e i).val ⊆ tetradUnion π e s ↔ i ∈ s := by
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (e i).val.card by rw [π.tetrad _ (e i).property]; decide)
    obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp (hs ha)
    have hij : i = j := by
      by_contra hn
      have hne : (e i).val ≠ (e j).val := fun he => hn (e.injective (Subtype.ext he))
      exact Finset.disjoint_left.mp (π.disjoint _ (e i).property _ (e j).property hne) ha haj
    exact hij ▸ hj
  · intro hi a ha
    exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩

theorem tetradUnion_injective : Function.Injective (tetradUnion π e) := by
  intro s t he
  ext i
  rw [← tetradUnion_mem π e s i, ← tetradUnion_mem π e t i, he]

def duadOctad (a : Duad) : Finset (Fin 24) := tetradUnion π e (duadSet a)

theorem duadOctad_injective : Function.Injective (duadOctad π e) :=
  (tetradUnion_injective π e).comp (by decide : Function.Injective duadSet)

theorem incident_octad_duad {l : Line} (hl : Incident l π) {A : Finset (Fin 24)}
    (hA : A ∈ l.parts) : ∃ a : Duad, duadOctad π e a = A := by
  obtain ⟨B, hB, C, hC, hBC, rfl⟩ := hl A hA
  obtain ⟨i, hi⟩ := e.surjective ⟨B, hB⟩
  obtain ⟨j, hj⟩ := e.surjective ⟨C, hC⟩
  have hij : i ≠ j := by rintro rfl; exact hBC (congrArg Subtype.val (hi.symm.trans hj))
  have complete : ∀ i j : Fin 6, i ≠ j → ∃ a : Duad, duadSet a = {i,j} := by decide
  obtain ⟨a, ha⟩ := complete i j hij
  refine ⟨a, ?_⟩
  simp [duadOctad, tetradUnion, ha, hi, hj]

def trioDuads (l : Line) : Finset Duad := Finset.univ.filter (fun a => duadOctad π e a ∈ l.parts)

theorem trioDuads_image {l : Line} (hl : Incident l π) :
    (trioDuads π e l).image (duadOctad π e) = l.parts := by
  ext A
  constructor
  · rintro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp ha).2
  · intro hA
    obtain ⟨a, rfl⟩ := incident_octad_duad π e hl hA
    exact Finset.mem_image.mpr ⟨a, by simpa [trioDuads] using hA, rfl⟩

theorem trioDuads_card {l : Line} (hl : Incident l π) : (trioDuads π e l).card = 3 := by
  rw [← Finset.card_image_of_injective _ (duadOctad_injective π e), trioDuads_image π e hl, l.card]

theorem trioDuads_disjoint {l : Line} {a b : Duad}
    (ha : a ∈ trioDuads π e l) (hb : b ∈ trioDuads π e l) (hab : a ≠ b) :
    Disjoint (duadSet a) (duadSet b) := by
  apply Finset.disjoint_left.mpr
  intro i hia hib
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (e i).val.card by rw [π.tetrad _ (e i).property]; decide)
  have huA : u ∈ duadOctad π e a := (tetradUnion_mem π e _ i).mpr hia hu
  have huB : u ∈ duadOctad π e b := (tetradUnion_mem π e _ i).mpr hib hu
  exact Finset.disjoint_left.mp
    (l.disjoint _ (Finset.mem_filter.mp ha).2 _ (Finset.mem_filter.mp hb).2
      ((duadOctad_injective π e).ne hab)) huA huB

private theorem syntheme_of_three (a b c : Duad)
    (hab : duadCollinear a b) (hac : duadCollinear a c) (hbc : duadCollinear b c) :
    ∃ s : Syntheme, synthemeDuads s = {a,b,c} := by decide +revert

theorem trioDuads_syntheme {l : Line} (hl : Incident l π) :
    ∃ s : Syntheme, synthemeDuads s = trioDuads π e l := by
  obtain ⟨a,b,c,hab,hac,hbc,hs⟩ := Finset.card_eq_three.mp (trioDuads_card π e hl)
  have ha : a ∈ trioDuads π e l := by simp [hs]
  have hb : b ∈ trioDuads π e l := by simp [hs]
  have hc : c ∈ trioDuads π e l := by simp [hs]
  obtain ⟨s,h⟩ := syntheme_of_three a b c
    ⟨hab, by rw [Finset.disjoint_iff_inter_eq_empty.mp (trioDuads_disjoint π e ha hb hab)]; rfl⟩
    ⟨hac, by rw [Finset.disjoint_iff_inter_eq_empty.mp (trioDuads_disjoint π e ha hc hac)]; rfl⟩
    ⟨hbc, by rw [Finset.disjoint_iff_inter_eq_empty.mp (trioDuads_disjoint π e hb hc hbc)]; rfl⟩
  exact ⟨s,h.trans hs.symm⟩

noncomputable def residueSyntheme (l : {l : Line // Incident l π}) : Syntheme :=
  (trioDuads_syntheme π e l.property).choose

theorem residueSyntheme_spec (l : {l : Line // Incident l π}) :
    synthemeDuads (residueSyntheme π e l) = trioDuads π e l.val :=
  (trioDuads_syntheme π e l.property).choose_spec

theorem residueSyntheme_injective : Function.Injective (residueSyntheme π e) := by
  intro l m he
  apply Subtype.ext
  apply line_parts_injective
  rw [← trioDuads_image π e l.property, ← trioDuads_image π e m.property,
    ← residueSyntheme_spec π e l, ← residueSyntheme_spec π e m, he]


theorem duadOctad_octad (a : Duad) : duadOctad π e a ∈ m24Blocks := by
  obtain ⟨i,j,hij,ha⟩ := Finset.card_eq_two.mp (duad_is_duad a)
  simpa [duadOctad, tetradUnion, ha] using
    π.octad _ (e i).property _ (e j).property
      (fun he => hij (e.injective (Subtype.ext he)))

theorem tetradUnion_disjoint {s t : Finset (Fin 6)} (h : Disjoint s t) :
    Disjoint (tetradUnion π e s) (tetradUnion π e t) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  obtain ⟨i,hi,hui⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨j,hj,huj⟩ := Finset.mem_biUnion.mp hv
  have hij : i ≠ j := fun he => Finset.disjoint_left.mp h hi (he ▸ hj)
  exact Finset.disjoint_left.mp
    (π.disjoint _ (e i).property _ (e j).property
      (fun he => hij (e.injective (Subtype.ext he)))) hui huj

theorem tetradUnion_univ : tetradUnion π e Finset.univ = Finset.univ := by
  apply Finset.ext
  intro u
  simp only [Finset.mem_univ, iff_true]
  have hu : u ∈ π.parts.biUnion id := π.cover.symm ▸ Finset.mem_univ u
  obtain ⟨A,hA,huA⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨i,hi⟩ := e.surjective ⟨A,hA⟩
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _, by simpa [hi] using huA⟩

private theorem syntheme_pair_disjoint (s : Syntheme) (a b : Duad)
    (ha : a ∈ synthemeDuads s) (hb : b ∈ synthemeDuads s) (hab : a ≠ b) :
    Disjoint (duadSet a) (duadSet b) := by decide +revert

/-- A perfect matching of the six actual tetrads yields an incident native trio. -/
def synthemeTrio (s : Syntheme) : Line where
  parts := (synthemeDuads s).image (duadOctad π e)
  card := by rw [Finset.card_image_of_injective _ (duadOctad_injective π e)]; exact (syntheme_is_partition s).1
  octad := by
    intro A hA
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
    exact duadOctad_octad π e a
  disjoint := by
    intro A hA B hB hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
    exact tetradUnion_disjoint π e
      (syntheme_pair_disjoint s a b ha hb (fun he => hne (congrArg _ he)))
  cover := by
    rw [Finset.image_biUnion]
    change (synthemeDuads s).biUnion (fun a => (duadSet a).biUnion (fun i => (e i).val)) = _
    rw [← Finset.biUnion_biUnion, (syntheme_is_partition s).2]
    exact tetradUnion_univ π e

theorem synthemeTrio_incident (s : Syntheme) : Incident (synthemeTrio π e s) π := by
  intro A hA
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨i,j,hij,ha⟩ := Finset.card_eq_two.mp (duad_is_duad a)
  refine ⟨(e i).val, (e i).property, (e j).val, (e j).property,
    fun he => hij (e.injective (Subtype.ext he)), ?_⟩
  simp [duadOctad, tetradUnion, ha]

theorem residueSyntheme_synthemeTrio (s : Syntheme) :
    residueSyntheme π e ⟨synthemeTrio π e s, synthemeTrio_incident π e s⟩ = s := by
  apply (by decide : Function.Injective synthemeDuads)
  rw [residueSyntheme_spec]
  apply Finset.image_injective (duadOctad_injective π e)
  exact trioDuads_image π e (synthemeTrio_incident π e s)

/-- Literal incident trios are the singular lines of the binary symplectic space.
The six letters label tetrads of this sextet, and every octad is their actual union. -/
noncomputable def residueEquiv : {l : Line // Incident l π} ≃ Syntheme :=
  Equiv.ofBijective (residueSyntheme π e)
    ⟨residueSyntheme_injective π e, fun s => ⟨⟨synthemeTrio π e s,
      synthemeTrio_incident π e s⟩, residueSyntheme_synthemeTrio π e s⟩⟩

theorem residueEquiv_incidence (l : {l : Line // Incident l π}) (a : Duad) :
    incident a (residueEquiv π e l) ↔ duadOctad π e a ∈ l.val.parts := by
  change a ∈ synthemeDuads (residueSyntheme π e l) ↔ _
  rw [residueSyntheme_spec]
  simp [trioDuads]

theorem residueEquiv_delta_one (l m : {l : Line // Incident l π}) :
    Delta 1 l.val m.val ↔ synthemeCollinear (residueEquiv π e l) (residueEquiv π e m) := by
  rw [syntheme_collinear_iff_common_duad]
  constructor
  · rintro ⟨hne, A, hA⟩
    obtain ⟨ha,hb⟩ := Finset.mem_inter.mp hA
    obtain ⟨a,rfl⟩ := incident_octad_duad π e l.property ha
    refine ⟨fun he => hne (congrArg (fun l => l.val.parts) ((residueEquiv π e).injective he)), a,
      (residueEquiv_incidence π e l a).mpr ha, (residueEquiv_incidence π e m a).mpr hb⟩
  · rintro ⟨hne,a,ha,hb⟩
    exact ⟨fun he => hne (congrArg (residueEquiv π e) (Subtype.ext (line_parts_injective he))),
      duadOctad π e a, Finset.mem_inter.mpr
        ⟨(residueEquiv_incidence π e l a).mp ha, (residueEquiv_incidence π e m a).mp hb⟩⟩

theorem residueEquiv_delta_two (l m : {l : Line // Incident l π}) (ht : Delta 2 l.val m.val) :
    Disjoint (synthemeDuads (residueEquiv π e l)) (synthemeDuads (residueEquiv π e m)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  exact Finset.disjoint_left.mp ht.1
    ((residueEquiv_incidence π e l a).mp ha) ((residueEquiv_incidence π e m a).mp hb)

/-- The literal native residue with its actual binary symplectic carrier. -/
noncomputable def residuePolarEquiv : {l : Line // Incident l π} ≃ BinaryLine :=
  (residueEquiv π e).trans synthemePolarEquiv

end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
